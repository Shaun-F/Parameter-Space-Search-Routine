(* ::Package:: *)

BeginPackage["SearchRoutine`"];

InitializeSearchRoutine::usage = "
Initialize the function, parameters, coordinates, parameter bounds, coordinate bounds, parameter space resolution, coordinate space resolution, chunk size, and Quantifier reltion.
function should be a symbolic expression. 
parametersList is a list of the parameters.
coordinatesList is a list of the coordinate variables.
paramBoundsList is a list of the intervals each parameter can range over in the form {{a,b}, {c,d}, {e,f}, etc.}
coordBoundsList is a list of the intervals each coordinate can range over in the form {{a,b},{c,d}, {e,f}, etc.}
paramResFloat is the resolution of the parameter space. In other words, the lattice spacing of the discretized parameter space.
coordResFloat is the resolution of the coordinate space. In other words, the lattice spacing of the discretized coordinate space. 
QuantifierRelation is the relation that must be satisfied over the entire coordinate space.
(Optional) CompilerTarget (def: 'C') is the compiler target of the Compile function
(Optional) chunkSizeInt (def: 1000) is an integer specifying how many parameter space lattice points should be contained within each chunk. 
(Optional) StartinChunk (def: 1) specifies the the chunk number to start at. Largely used for debugging purposes.";

SetupParallelization::usage = "setup the subkernels, distribute definitions, initialize relevant parallelization parameters. No inputs.";
ExecuteSearch::usage = "Execute the parameter space search.";

helpSearchRoutine::usage = "
To begin, execute InitializeSearchRoutine[...] with the desired arguments (See '?InitializeSearchRoutine')
Once this function is executed, the search routine will be initialized. The next step is to execute SetupParallelization[], with no parameters. This sets up the parallelization
	and prepares the search routine for execution over multiple kernels. The number of subkernels is equal to the number of CPU cores on your machine.

Once the search routine is prepared, execute the function ExecuteSearch[]. This runs the search routine and returns either the first set of parameters that satisfies the 
	quantifier relation, or returns $Failed which means the quantifier relations was not satisfied over the given parameter space and coordinate space regions with the given
	resolution.";


Begin["Private`"];
ListScalar[List_]:=If[Length@List==1, List[[1]], List[[-1]]*ListScalar[List[[1;;Length@List-1]]]]

InitializeSearchRoutine[func_, parametersList_, coordinatesList_, paramBoundsList_, coordBoundsList_, paramResFloat_, coordResFloat_,  QuantifierRelation_, CompilerTarget_:"C", chunkSizeInt_:100,StartingChunk_:1] := 
	Module[{},
		ClearAll[nParameterChunks,nParameterLatticePoints,PartitionedParameterIntervals,DiscretizedCoordinateSpace,QuantifierOverCoordSpace,ParameterSpaceChunks,numChunks,nParams,nParamSpacePartitions, parameters, paramRes, paramBounds, coordBounds, coordRes, coords];
		
		function = func;
		parameters = parametersList;
		coords = coordinatesList;
		paramBounds = paramBoundsList;
		coordBounds = coordBoundsList;
		paramRes = paramResFloat;
		coordRes = coordResFloat;
		chunkSize = chunkSizeInt;
		Quantifier = QuantifierRelation;
		
		(*Optional Function Params*)
		CompTarget = CompilerTarget;
		startchunk = StartingChunk;
		
		functiontoscanPure = 
		Function[Evaluate@Join[coords, parameters], Evaluate@function];
		
		ParameterRanges = 
			With[{inv = paramBounds},
				Table[
					Range[inv[[All,1]][[i]], inv[[All,2]][[i]], paramRes], 
					{i,1,Length@parameters}
					]
				];
		CoordinateRanges = 
			With[{inv = coordBounds},
				Table[
					Range[inv[[All,1]][[i]], inv[[All,2]][[i]], coordRes], {i,1,Length@coords}
					]
				];
		
		nParameterLatticePoints = Round@ ListScalar[Length/@ParameterRanges];(*the total number of lattice points of the parameter space*)
		nCoordinateLatticePoints = Round@ListScalar[Length/@CoordinateRanges];
		nParameterChunks = Ceiling@((nParameterLatticePoints/chunkSize)^((1/Length@parameters)));(*number of chunks of each individual parameter*)
		
		Print["\nParameter space co-ordinates: \n\t\t"<>ToString@parameters];
		Print["\nDimension of parameter space: \n\t\t"<>ToString@Dimensions@parameters];
		Print["\nNumber of parameter space lattice points: \n\t\t"<>ToString@nParameterLatticePoints];
		Print["\nNumber of Co-ordinate space lattic points: \n\t\t"<>ToString@nCoordinateLatticePoints];
		Print["\nProjected RAM used (MB): \n\t\t"<> ToString[
		{"Quantifier: ",
		Evaluate["\t\t\t"<>ToString[N@(ByteCount[functiontoscanPure]/1000000)]],
		 " \t\tQuantized Coord Space: ", 
		 "\t\t\t"<>ToString[1/1000000 ByteCount[ConstantArray[1., Length@coords]]*ListScalar[(coordBounds[[All,2]]-coordBounds[[All,1]])/coordRes]],
		  "\t\tQuantized Parameter Space: ", 
		  "\t\t\t"<>ToString[1/1000000 ByteCount[ConstantArray[1., Length@coords]]*ListScalar[(paramBounds[[All,2]]-paramBounds[[All,1]])/paramRes]]
		  }//Column]];
		Print["\nNumber of chunks each parameter is split into: \n\t\t"<>ToString@nParameterChunks];
	]
	

SetupParallelization[]:=
	Module[{},
		
		NotebookPathString = NotebookDirectory[];
		Off[LaunchKernels::nodef];
		CloseKernels[];
		LaunchKernels[$ProcessorCount];
		On[LaunchKernels::nodef];
		
		PrintTemporary["Building coordinate space lattice ..."];
		DiscretizedCoordinateSpace = 
			If[Length@coords>1,Tuples[CoordinateRanges], CoordinateRanges[[1]]];

		PrintTemporary["Distributing function over coordinate lattice and compiling to C code ..."];
		FunctionOverCoordSpace = 
			functiontoscanPure[Sequence@@Flatten[{#, parameters}]]&/@DiscretizedCoordinateSpace;
		CFunctionOverCoordSpace = 
		Compile@@{parameters, FunctionOverCoordSpace, CompilationTarget->CompTarget,"RuntimeOptions"->"Speed",
			RuntimeAttributes->{Listable}};
		
		(*
		https://mathematica.stackexchange.com/questions/109598/lazy-form-of-tuples-outer-to-loop-over-list-of-lists
		*)
		ClearAll[next, multiDims, multiIndex, take];
		next[{left_,_},dim_]:={left-dim*(#-1),#}&[IntegerPart[(left-1)/dim]+1];
		
		multiDims[dims_]:=Rest@Reverse@FoldList[Times,1,Reverse@dims];

		multiIndex[pos_,dims:{__Integer}]:=Rest@FoldList[next,{pos,0},multiDims@dims][[All,2]];

		take[lists:{__List},{start_,end_}]:=With[{rend=Min[end,Times@@Map[Length,lists]]},Transpose@MapThread[Part,{lists,multiIndex[Range[start,rend],Length/@lists]}]];

		(*Distribute the variable and function definitions to the various subkernels*)
		DistributeDefinitions[next, multiDims, multiIndex, take,parameters,ParameterRanges, paramRes, CFunctionOverCoordSpace,coords,DiscretizedCoordinateSpace, NotebookPathString];

		ChunkSelection = 
			With[{nchunks = 1/chunkSize (nParameterLatticePoints-Mod[nParameterLatticePoints, chunkSize])},
				Append[Array[{(#-1)*chunkSize+1, #*chunkSize}&, nchunks], {nchunks*chunkSize, nParameterLatticePoints}]];
		
		numChunks = Length@ChunkSelection;

		Print["Number of chunks the parameter space is split into: ", numChunks];
		
		Print["Setup complete. Proceed with execution via ExecuteSearch[]"];
	]
	
(* Execute the parallelized search*)
ExecuteSearch[] :=  
	Module[{},
		PrintTemporary["Executing over ",$KernelCount, " Kernels"];
		ClearAll[ParallelizedResult, kernels, CurrentStep];
		ParallelEvaluate[Off[General::munfl]];
		
		kernels = ParallelTable[$KernelID-> i, {i, $KernelCount}];
		CurrentStep = ConstantArray[0, $KernelCount];
		SetSharedVariable[kernels,CurrentStep];
		PrintTemporary@Dynamic[CurrentStep//Column];
		
		(*Run the parallelized search routine*)
		ParallelizedResult = 
			ParallelTry[
				((*CurrentStep[[$KernelID/.kernels]]="Kernel "<>ToString[$KernelID]<>" executing chunk "<>ToString[#];*)
					With[{parameterSpaceSubset = take[ParameterRanges, #]},
						subresult = (AllTrue[CFunctionOverCoordSpace@@#,Positive])&/@parameterSpaceSubset;
						Result = First[Pick[parameterSpaceSubset, subresult],{}];
						If[Length@Result>0, 
							Result,
							 $Failed]
						]
				)&,
				ChunkSelection[[startchunk;;All]]]//Timing;
		Print[
		"\nTime for the parameter space to be searched with given resolutions and bounds: \n\t\t",ParallelizedResult[[1]]/60, " Minutes",
		 "\n\nResult of search: \n\n",ToString[Thread[parameters== ParallelizedResult[[2]]]]
		 ]
	]
	
End[];
EndPackage[];
