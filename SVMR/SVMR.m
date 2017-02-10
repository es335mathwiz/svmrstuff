(* Wolfram Language Package *)

(* Created by the Wolfram Workbench Feb 6, 2017 *)

BeginPackage["SVMR`", {"JLink`"}]
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




End[]

EndPackage[]

