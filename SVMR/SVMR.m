(* Wolfram Language Package *)

(* Created by the Wolfram Workbench Feb 6, 2017 *)

BeginPackage["SVMR`", {"JLink`"}]

doLinearStaelin::usage = "doLinearStaelin  "


doSigmoid::usage = "doSigmoid  "

doRBF::usage = "doRBF  "

doPoly::usage = "doPoly  "


doLinear::usage = "doLinear  "
(* Exported symbols added here with SymbolName::usage *) 

Begin["`Private`"]
(* Implementation of the package *)


genPlusVars[numExamples_Integer]:=
Table[
Symbol["alphaPlus$"<>ToString[ii]],
{ii,numExamples}]

genMinusVars[numExamples_Integer]:=
Table[
Symbol["alphaMinus$"<>ToString[ii]],
{ii,numExamples}]

genXVars[numFeatures_Integer]:=
Table[
Symbol["xx$"<>ToString[ii]],
{ii,numFeatures}]


applyKernel[xData_?MatrixQ,(kernelFunc_Function|kernelFunc_Symbol)]:=
kernelFunc[xData,xData]/;And[Length[xData]>0,Length[xData[[1]]]>0]

interactAlphas[numExamples_Integer]:=
With[{pVars=genPlusVars[numExamples],mVars=genMinusVars[numExamples]},
With[{diff=pVars-mVars},
Table[diff[[ii]]*diff[[jj]],{ii,numExamples},{jj,numExamples}]]]

dotProdKernel=Function[{xx,yy},Transpose[xx] . yy];



makeSymbolicKernel[]:=
With[{myX=Unique["xx"],myY=Unique["yy"]},
	 Apply[Function,{{myX,myY},ffff[myX,myY]}]]

makePolynomialKernel[aPow_Integer]:=
With[{myX=Unique["xx"],myY=Unique["yy"]},
Apply[Function,{{myX,myY},(1+Transpose[myX] . myY)^aPow}]]


makeRBFKernel[aRadius_Integer]:=
Function[{myX,myY},E^(-Outer[Norm[Plus[#1,#2]]&,Transpose[myX],-Transpose[myY],1]/(2*(aRadius^2)))]

xQuadTerm[xData_?MatrixQ,(theKernel_Function|theKernel_Symbol)]:=
With[{kernApp=applyKernel[xData,theKernel],
theAlphas=interactAlphas[Length[xData[[1]]]]},
(-1/2)*(Plus @@ Flatten[kernApp*theAlphas])]/;
And[Length[xData]>0,Length[xData[[1]]]>0]


epsTerm[numExamples_Integer,(epsilon_?NumberQ|epsilon_Symbol)]:=
With[{pVars=genPlusVars[numExamples],mVars=genMinusVars[numExamples]},
-epsilon*Plus @@ (pVars+mVars)]





yTerm[yData_?VectorQ]:=
With[{numExamples=Length[yData]},
With[{pVars=genPlusVars[numExamples],mVars=genMinusVars[numExamples]},
-(Plus @@ (yData * (pVars-mVars)))]]

cnstrnts[numExamples_Integer,(CC_?NumberQ|CC_Symbol)]:=
With[{pVars=genPlusVars[numExamples],mVars=genMinusVars[numExamples]},
Join[0<=#<=CC& /@pVars,0<=#<=CC& /@mVars, {(Plus @@ (pVars-mVars))==0}]]

$zeroTol=10.0^(-8);
Options[theBasicQPSol]={maximizer->FindMaximum}
theBasicQPSol[xData_?MatrixQ,yData_?VectorQ,
			  (theKernel_Function),(CC_?NumberQ),(epsilon_?NumberQ),
			  opts:OptionsPattern[{theBasicQPSol,FindMaximum,NMaximize}]]:=
With[{numExamples=Length[yData]},
With[{epsPart=epsTerm[numExamples,epsilon],
yPart=yTerm[yData],
xPart=xQuadTerm[xData,theKernel],
cns=cnstrnts[numExamples,CC],
	  vars=(*{#,0}&/@*)Join[genPlusVars[numExamples],
							genMinusVars[numExamples]]},
With[{qpGuts={xPart+epsPart+yPart,And @@cns}},
	 With[{qpSol=
Switch[OptionValue[maximizer],
NMaximize,NMaximize[qpGuts,vars,Sequence@@FilterRules[{opts},Options[NMaximize]]],
FindMaximum,FindMaximum @@ {qpGuts,vars,Sequence@@FilterRules[{opts},Options[NMaximize]]},
	   _,Throw["maximizer unknown="<>ToString[OptionValue[maximizer]]]]
		  },
With[{qpSubs=qpSol[[2]]},
{qpSubs,cnstrctF[qpSubs,xData,yData,theKernel,CC,epsilon]}
]]]]]/;
And[Length[xData[[1]]]==Length[yData],Length[yData]>0,
CC>$zeroTol,epsilon>$zeroTol]


cnstrctBasicQP[xData_?MatrixQ,yData_?VectorQ,(theKernel_Function|theKernel_Symbol),(CC_?NumberQ|CC_Symbol),(epsilon_?NumberQ|epsilon_Symbol)]:=
With[{numExamples=Length[yData]},
With[{epsPart=epsTerm[numExamples,epsilon],
yPart=yTerm[yData],
xPart=xQuadTerm[xData,theKernel],
cns=cnstrnts[numExamples,CC]},
{xPart+epsPart+yPart,cns}]]



$NtolVal=50;

inTube[qpSubs:{(_->_)...},tol_Rational]:=
inTube[qpSubs,N[tol,$NtolVal]]


inTube[qpSubs:{(_->_)...},tol_Real:$zeroTol]:=
With[{numExamples=Length[qpSubs]/2},
With[{allPairs=
Transpose[{genPlusVars[numExamples],genMinusVars[numExamples]}]/.qpSubs},
Union[Flatten[Position[And[#[[1]]<tol,#[[2]]<tol]&/@allPairs,True]]]]]



outsideTube[qpSubs:{(_->_)...},CC_?NumberQ,tol_Rational]:=
outsideTube[qpSubs,CC,N[tol,$NtolVal]]

outsideTube[qpSubs:{(_->_)...},CC_?NumberQ,tol_Real:$zeroTol]:=
With[{numExamples=Length[qpSubs]/2},
With[{allPairs=
Transpose[{genPlusVars[numExamples],genMinusVars[numExamples]}]/.qpSubs},
Union[Flatten[Position[
Or[CC-#[[1]]<tol,CC-#[[2]]<tol]&/@allPairs,True]]]]]


onPlusBoundaryTube[
qpSubs:{(_->_)...},CC_?NumberQ,tol_Rational]:=
onPlusBoundaryTube[
qpSubs,CC,N[tol,$NtolVal]]

onPlusBoundaryTube[
qpSubs:{(_->_)...},CC_?NumberQ,tol_Real:$zeroTol]:=
With[{ob=onBoundaryTube[qpSubs,CC,tol]},If[ob=={},{},
ob[[Flatten[Position[chkAlphas[qpSubs,CC,tol],{1,2}]]]]]]




onMinusBoundaryTube[
qpSubs:{(_->_)...},CC_?NumberQ,tol_Rational]:=
onMinusBoundaryTube[
qpSubs,CC,N[tol,$NtolVal]]

onMinusBoundaryTube[
qpSubs:{(_->_)...},CC_?NumberQ,tol_Real:$zeroTol]:=
With[{ob=onBoundaryTube[qpSubs,CC,tol]},
If[ob=={},{},
ob[[Flatten[Position[chkAlphas[qpSubs,CC,tol],{2,1}]]]]]]


chkAlphas[
qpSubs:{(_->_)...},CC_?NumberQ,tol_Rational]:=
chkAlphas[qpSubs,CC,N[tol,$NtolVal]]

chkAlphas[qpSubs:{(_->_)...},CC_?NumberQ,tol_Real:$zeroTol]:=
With[{numExamples=Length[qpSubs]/2},
With[{
alp=genPlusVars[numExamples]/.qpSubs,
alpStar=genMinusVars[numExamples]/.qpSubs,
toChk=Complement[Range[Length[qpSubs]/2],
Join[inTube[qpSubs,tol],outsideTube[qpSubs,CC,tol]]]
},
With[{pairs=Transpose[{alp,alpStar}][[toChk]]},
Ordering/@pairs
]]]




onBoundaryTube[qpSubs:{(_->_)...},CC_?NumberQ,tol_Rational]:=
onBoundaryTube[qpSubs,CC,N[tol,$NtolVal]]


onBoundaryTube[qpSubs:{(_->_)...},CC_?NumberQ,tol_Real:$zeroTol]:=
Complement[Range[Length[qpSubs]/2],
Join[inTube[qpSubs,tol],outsideTube[qpSubs,CC,tol]]]


supportVectors[xData_?MatrixQ,yData_?VectorQ,
qpSubs:{(_->_)...},CC_?NumberQ,tol_Rational]:=
supportVectors[xData,yData,
qpSubs,CC,N[tol,$NtolVal]]

supportVectors[xData_?MatrixQ,yData_?VectorQ,
qpSubs:{(_->_)...},CC_?NumberQ,tol_Real:$zeroTol]:=
With[{indices=Union[Join[onBoundaryTube[qpSubs,CC,tol],
outsideTube[qpSubs,CC,tol]]]},If[indices=={},{},
Append[xData[[All,indices]],yData[[indices]]]]]


cnstrctF[qpSubs_List,xData_?MatrixQ,yData_?VectorQ,
theKernel_Function,CC_?NumberQ,epsilon_?NumberQ]:=
With[{xvars=Transpose[{genXVars[Length[xData]]}],
numExamples=Length[xData[[1]]]},
With[{pVars=genPlusVars[numExamples],mVars=genMinusVars[numExamples]},
With[{kernelPart=Flatten[theKernel[Transpose[{#}],xvars]&/@Transpose[xData]]},
	 Function @@{Flatten[xvars],(-1)*((pVars-mVars)/.qpSubs) . kernelPart+
approxB[qpSubs,xData,yData,theKernel,CC,epsilon]}]]]/;
And[Length[xData]>0,Length[xData[[1]]]>0]

approxB[qpSubs_List,xData_?MatrixQ,yData_?VectorQ,
theKernel_Function,CC_?NumberQ,epsilon_?NumberQ]:=
With[{minusBs=(Flatten[
yData[[onMinusBoundaryTube[qpSubs,CC]]] +
((wExprn[xData,theKernel,Transpose[{#}]]/.qpSubs)&/@
Transpose[xData[[All,onMinusBoundaryTube[qpSubs,CC]]]])+
epsilon]),
plusBs=(Flatten[
yData[[onPlusBoundaryTube[qpSubs,CC]]] +
((wExprn[xData,theKernel,Transpose[{#}]]/.qpSubs)&/@
Transpose[xData[[All,onPlusBoundaryTube[qpSubs,CC]]]])-
epsilon])},Print["approxB:",{minusBs,plusBs}];
	 With[{finite=DeleteCases[{Max[minusBs],Min[plusBs]},Infinity|-Infinity]},If[Length[finite]==0,0,(Plus @@finite)/Length[finite]]]]


wExprn[xData_?MatrixQ]:=
With[{numExamples=Length[xData[[1]]]},
With[{pVars=genPlusVars[numExamples],mVars=genMinusVars[numExamples]},
(pVars-mVars).Transpose[xData]]]/;
And[Length[xData]>0,Length[xData[[1]]]>0]


wExprn[xData_?MatrixQ,kernelFunc_Function,particularX_?MatrixQ]:=
With[{numExamples=Length[xData[[1]]]},
With[{pVars=genPlusVars[numExamples],mVars=genMinusVars[numExamples]},
Flatten[
	(pVars-mVars). (kernelFunc[Transpose[{#1}],particularX]&/@Transpose[xData])	
]]]/;
And[Length[xData]>0,Length[xData[[1]]]>0]





hvBlocks[xData_?MatrixQ,yData_?VectorQ,hh_Integer,vv_Integer,ii_Integer]:=
With[{rngs=cmpHVDataRanges[Length[yData],hh,vv,ii]},
{{xData[[All,rngs[[1]]]],yData[[rngs[[1]]]]},
{xData[[All,rngs[[2]]]],yData[[rngs[[2]]]]}}]/;
And[Length[xData[[1]]]==Length[yData],hh>=0,vv>=0,
Length[yData]-(hh+vv)>=ii>=(hh+vv+1)]

cmpHVDataRanges[lenData_Integer,hh_Integer,vv_Integer,ii_Integer]:=
With[{keepers=Range[ii-(hh+vv),ii+(hh+vv)]},
{keepers,Complement[Range[lenData],keepers]}]/;
And[hh>=0,vv>=0,
lenData-(hh+vv)>=ii>=(hh+vv+1)]

(* from notebook  *)
gen3D[paramRanges : {{_?NumberQ, _?NumberQ} ..}] :=
 With[{theTrips = {#[[1]], (#[[1]] + #[[2]])/2, #[[2]]} & /@ 
     paramRanges},
  theTrips]
gen2D[paramRanges : {{_?NumberQ, _?NumberQ} ..}] :=
 With[{theTwos = {#[[1]] + (#[[2]] - #[[1]])/4, #[[
         2]] - (#[[2]] - #[[1]])/4} & /@ paramRanges},
  theTwos]
outerFirstPair[xx_?MatrixQ, yy : {_?NumberQ ..}] := 
    Flatten[Outer[Append, xx, yy, 1], 1];
allOuters[xx : {{_?NumberQ ..} ..}] := Fold[outerFirstPair, {{}}, xx]
staelinPoints[paramRanges : {{_?NumberQ, _?NumberQ} ..}] := 
 With[{threeDs = allOuters[gen3D[paramRanges]], 
   twoDs = allOuters[gen2D[paramRanges]]}, Join[threeDs, twoDs]]
practicalSelection[yVals_?VectorQ, sigEps_?NumberQ] := 
 With[{stdevY = StandardDeviation[yVals], meanY = Mean[yVals], 
   nn = Length[yVals]}, 
  With[{cVal = 
     Max[Abs[meanY - 3*stdevY], Abs[meanY + 3*stdevY]]}, {cVal, 
    3*sigEps*Sqrt[Log[nn]/nn]}]]
    
  
doLinear[xVals_?MatrixQ, yVals_?VectorQ, paramVals_?VectorQ, 
  nFolds_Integer] := Module[{svmtLinear, modLinear},
  svmtLinear = JavaNew["libsvm.trainGuts"];
  svmtLinear[mmaUreadUproblemLinear[xVals, yVals, paramVals]];
  modLinear = 
   libsvm`svm`svmUtrain[svmtLinear[prob], svmtLinear[param]];
  {svmtLinear, modLinear, 
   libsvm`svm`svmUpredict[modLinear, #] & /@ xVals, 
   libsvm`svm`svmUcrossUvalidation[svmtLinear[prob], 
    svmtLinear[param], nFolds]}]
    
   Print["needs to include initial"]; 
    doLinearStaelin[{{ccWasBest_?NumberQ,epsWasBest_?NumberQ},wasBestVal_?NumberQ},
  pRngs : {{ccLow_?NumberQ, ccHigh_?NumberQ}, {epsLow_?NumberQ, 
     epsHigh_?NumberQ}},forMin_] := Module[{stPts = staelinPoints[pRngs]},
     With[{mBy=MinimalBy[stPts,forMin]},
     		{{mBy[[1]],forMin[mBy[[1]]]},reCenter[pRngs,mBy[[1]]],forMin}]]
  
  reCenter[pRngs : {{ccLow_?NumberQ, ccHigh_?NumberQ}, {epsLow_?NumberQ, 
     epsHigh_?NumberQ}},theBest:{bestCC_?NumberQ,bestEps_?NumberQ}]:=
     With[{newLens = (#[[2]] - #[[1]])/2 & /@ pRngs},
     MapThread[reCenterOne,{pRngs,theBest,newLens}]]
     
     	reCenterOne[{lowVal_?NumberQ,highVal_?NumberQ},bestVal_?NumberQ,width_?NumberQ]:=
     	If[bestVal-width/2<lowVal,{lowVal,lowVal+width},If[bestVal+width/2>highVal,{highVal-width,highVal},
     		{bestVal-width/2,bestVal+width/2}]]
     	
     
(*
  doLinearStaelin[
  pRngs : {{ccLow_?NumberQ, ccHigh_?NumberQ}, {epsLow_?NumberQ, 
     epsHigh_?NumberQ}},forMin_] := Module[{stPts = staelinPoints[pRngs]},
     With[{mBy=MinimalBy[stPts,forMin]},
     		{mBy[[1]],
  Transpose[{stPts, forMin /@ stPts}],reCenter[pRngs,mBy[[1]]]}]]


doLinearStaelin[
  pRngs : {{ccLow_?NumberQ, ccHigh_?NumberQ}, {epsLow_?NumberQ, 
     epsHigh_?NumberQ}}] := 
 Module[{stPts = staelinPoints[pRngs], 
   newLens = (#[[2]] - #[[1]])/2 & /@ pRngs},
  With[{minBy =
     MinimalBy[stPts, forMinLinear]}, Print["minBy=", minBy];
   If[Length[minBy] =!= 1, 
    Throw["minBy not singleton:" <> ToString[minBy]],
    With[{toLeft = pRngs[[1]] - (minBy[[1]] - newLens), 
      toRight = (minBy[[1]] + newLens) - pRngs[[2]]}, {minBy, toLeft, 
      toRight}]]]]*)
      
      doPoly[xVals_?MatrixQ, yVals_?VectorQ, paramVals_?VectorQ, 
  nFolds_Integer] := Module[{svmtPoly, modPoly},
  svmtPoly = JavaNew["libsvm.trainGuts"];
  svmtPoly[mmaUreadUproblemPoly[xVals, yVals, paramVals]];
  modPoly = libsvm`svm`svmUtrain[svmtPoly[prob], svmtPoly[param]];
  {svmtPoly, modPoly, libsvm`svm`svmUpredict[modPoly, #] & /@ xVals, 
   libsvm`svm`svmUcrossUvalidation[svmtPoly[prob], svmtPoly[param], 
    nFolds]}]

 
 doRBF[xVals_?MatrixQ, yVals_?VectorQ, paramVals_?VectorQ, 
  nFolds_Integer] := Module[{svmtRBF, modRBF},
  svmtRBF = JavaNew["libsvm.trainGuts"];
  svmtRBF[mmaUreadUproblemRBF[xVals, yVals, paramVals]];
  modRBF = libsvm`svm`svmUtrain[svmtRBF[prob], svmtRBF[param]];
  {svmtRBF, modRBF, libsvm`svm`svmUpredict[modRBF, #] & /@ xVals, 
   libsvm`svm`svmUcrossUvalidation[svmtRBF[prob], svmtRBF[param], 
    nFolds]}]

 
 doSigmoid[xVals_?MatrixQ, yVals_?VectorQ, paramVals_?VectorQ, 
  nFolds_Integer] := Module[{svmtSigmoid, modSigmoid},
  svmtSigmoid = JavaNew["libsvm.trainGuts"];
  svmtSigmoid[mmaUreadUproblemSigmoid[xVals, yVals, paramVals]];
  modSigmoid = 
   libsvm`svm`svmUtrain[svmtSigmoid[prob], svmtSigmoid[param]];
  {svmtSigmoid, modSigmoid, 
   libsvm`svm`svmUpredict[modSigmoid, #] & /@ xVals, 
   libsvm`svm`svmUcrossUvalidation[svmtSigmoid[prob], 
    svmtSigmoid[param], nFolds]}]

Sigmoid[cc_?NumberQ, eps_?NumberQ, gamma_?NumberQ, 
  coeff_?NumberQ, degree_?NumberQ] := 
 Norm[doSigmoid[allCX, Flatten[allCY], {cc, eps}, 2][[3]]]
 
End[]

EndPackage[]

