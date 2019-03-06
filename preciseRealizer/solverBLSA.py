# Notices:
#
# Copyright 2019 United States Government as represented by the Administrator
# of the National Aeronautics and Space Administration. All Rights Reserved.
#
# Disclaimers:
#
# No Warranty: THE SUBJECT SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY
# OF ANY KIND, EITHER EXPRESSED, IMPLIED, OR STATUTORY, INCLUDING, BUT NOT
# LIMITED TO, ANY WARRANTY THAT THE SUBJECT SOFTWARE WILL CONFORM TO
# SPECIFICATIONS, ANY IMPLIED WARRANTIES OF MERCHANTABILITY, FITNESS FOR A
# PARTICULAR PURPOSE, OR FREEDOM FROM INFRINGEMENT, ANY WARRANTY THAT THE
# SUBJECT SOFTWARE WILL BE ERROR FREE, OR ANY WARRANTY THAT DOCUMENTATION, IF
# PROVIDED, WILL CONFORM TO THE SUBJECT SOFTWARE. THIS AGREEMENT DOES NOT, IN
# ANY MANNER, CONSTITUTE AN ENDORSEMENT BY GOVERNMENT AGENCY OR ANY PRIOR
# RECIPIENT OF ANY RESULTS, RESULTING DESIGNS, HARDWARE, SOFTWARE PRODUCTS OR
# ANY OTHER APPLICATIONS RESULTING FROM USE OF THE SUBJECT SOFTWARE. FURTHER,
# GOVERNMENT AGENCY DISCLAIMS ALL WARRANTIES AND LIABILITIES REGARDING
# THIRD-PARTY SOFTWARE, IF PRESENT IN THE ORIGINAL SOFTWARE, AND DISTRIBUTES
# IT "AS IS."
#
# Waiver and Indemnity: RECIPIENT AGREES TO WAIVE ANY AND ALL CLAIMS AGAINST
# THE UNITED STATES GOVERNMENT, ITS CONTRACTORS AND SUBCONTRACTORS, AS WELL AS
# ANY PRIOR RECIPIENT. IF RECIPIENT'S USE OF THE SUBJECT SOFTWARE RESULTS IN
# ANY LIABILITIES, DEMANDS, DAMAGES, EXPENSES OR LOSSES ARISING FROM SUCH USE,
# INCLUDING ANY DAMAGES FROM PRODUCTS BASED ON, OR RESULTING FROM, RECIPIENT'S
# USE OF THE SUBJECT SOFTWARE, RECIPIENT SHALL INDEMNIFY AND HOLD HARMLESS THE
# UNITED STATES GOVERNMENT, ITS CONTRACTORS AND SUBCONTRACTORS, AS WELL AS ANY
# PRIOR RECIPIENT, TO THE EXTENT PERMITTED BY LAW. RECIPIENT'S SOLE REMEDY FOR
# ANY SUCH MATTER SHALL BE THE IMMEDIATE, UNILATERAL TERMINATION OF THIS
# AGREEMENT.

import sys
import math
import re
from decimal import *
from ToSinglePrecisionConstants import *
from library import *

def encodeNewVariable(var,isFP):
	encodingCurrentVar=(
		"(declare-const "+str(var)+" Real)\n"
		"(declare-const abs-"+str(var)+" Real)\n"
		"(declare-const two-to-exp-p-minus-e-"+str(var)+" Real)\n"
		"(assert (=> (>= "+str(var)+" 0.0) (= abs-"+str(var)+" "+str(var)+")))\n"
		"(assert (=> (< "+str(var)+" 0.0) (= abs-"+str(var)+" (- "+str(var)+"))))\n\n")

	encodingCurrentVar=encodingCurrentVar+encodeDomainAndRanges(var,variablesFP[var],precisionFP[var])

	mantissaPrecision=precisionFP[var][0]
	exponentPrecision=precisionFP[var][1]

	valueSmallestFloat=Decimal(2**(-mantissaPrecision)*(2**-(2**(exponentPrecision-1)-1-1)))
	valueBiggestFloat=Decimal((2-(2**-mantissaPrecision))*2**(2**(exponentPrecision-1)-1))

	lowerValue=max(getAbsLowerBound(variablesFP[var]),valueSmallestFloat)
	lower=strFormatFromDecimal(lowerValue)

	upperValue=min(getAbsUpperBound(variablesFP[var]),valueBiggestFloat)
	upper=strFormatFromDecimal(upperValue)

	tmpValue=int(math.log(upperValue,2))
	tmpExp=tmpValue+1
	tmpValue=Decimal(2**(tmpExp))
	tmpStr=strFormatFromDecimal(tmpValue)

	powers=computePowers(lowerValue,tmpValue)

	if ActivateBinarySearch=="True":
		bs=binarySearch(str(var),powers,1,len(powers)-1,mantissaPrecision)
		bs="(assert \n"+bs+" )\n\n"
		encodingCurrentVar=encodingCurrentVar+bs+"\n"
	else:
		while tmpValue>lowerValue:
			encodingCurrentVar=encodingCurrentVar+"(assert (=> (and (<= "+strFormatFromDecimal(Decimal((2**(tmpExp-1))))+" abs-"+str(var)+") (< abs-"+str(var)+" "+tmpStr+")) (= two-to-exp-p-minus-e-"+str(var)+" "+strFormatFromDecimal(Decimal(2**(mantissaPrecision-(tmpExp-1))))+")))\n"
			tmpExp=tmpExp-1
			tmpValue=Decimal(2**(tmpExp))
			tmpStr=strFormatFromDecimal(tmpValue)

	if isFP:
		encodingCurrentVar=encodingCurrentVar+ "(assert (= (to_real ( "+str(smtRoundingMode)+" (* "+str(var)+" two-to-exp-p-minus-e-"+str(var)+"))) (* "+str(var)+" two-to-exp-p-minus-e-"+str(var)+")))\n\n\n"
	return encodingCurrentVar

# l & r have to be the indices of the limits of the array
def binarySearch (namevar,arr, l, r,maxVal,space=" "):
	if l < r:
		mid = l + (r - l)/2
		return "(ite (< abs-"+namevar+" "+strFormatFromDecimal(Decimal(2**(arr[mid])))+")\n"+space+binarySearch(namevar,arr,l,mid,maxVal,space+"  ")+"\n"+space+binarySearch(namevar,arr,mid+1,r,maxVal,space+"  ")+")"

	if r==l:
		return (
			"(= two-to-exp-p-minus-e-"+namevar+" "+strFormatFromDecimal(Decimal(2**(maxVal-arr[r-1])))+")"
		)

def initiateTempVarForArithmeticOperation(tempVar,operation,precOp):
	if precOp=="single":
		precisionFP[tempVar]=(int(singleMantissaPrecision),int(singleExponentPrecision))

		biggestFloat=Decimal((2-(2**-singleMantissaPrecision))*2**(2**(singleExponentPrecision-1)-1))
		NegBiggestFloat=Decimal(-(2-(2**-singleMantissaPrecision))*2**(2**(singleMantissaPrecision-1)-1))

		res=""+strFormatFromDecimal(NegBiggestFloat)+","+strFormatFromDecimal(biggestFloat)
		variablesFP[tempVar]=res
	elif precOp=="double":
		precisionFP[tempVar]=(int(doubleMantissaPrecision),int(doubleExponentPrecision))

		biggestFloat=Decimal((2-(2**-doubleMantissaPrecision))*2**(2**(doubleExponentPrecision-1)-1))
		NegBiggestFloat=Decimal(-(2-(2**-doubleMantissaPrecision))*2**(2**(doubleExponentPrecision-1)-1))

		res=""+strFormatFromDecimal(NegBiggestFloat)+","+strFormatFromDecimal(biggestFloat)
		variablesFP[tempVar]=res
	else:
		exit("only single or double precision supported")
	tmp=encodeNewVariable(tempVar,False)
	retEncoding=tmp+"\n"+"(assert (= "+tempVar+" "+operation+"))"
	return retEncoding

smtRoundingMode=str(sys.argv[1]) #rounding modes for the analysis ex."rnd-to-zero"
nameFile=str(sys.argv[2]) #name of the config file
ActivateBinarySearch=str(sys.argv[3]) #activate binary search

roundingModes=defineRoundingModes()

setContextForRoundingMode(smtRoundingMode)

roundingModesEncoding="(set-option :produce-models true)\n\n"+roundingModes[smtRoundingMode]+"\n\n"
AbsoluteValueFunctionEncoding="(define-fun myabs ((X Real)) Real (ite (> X 0) X (- 0 X)))\n"

precisionFP=dict()
variablesFP=dict()
variablesReal=dict()

with open(nameFile,"r+") as content_file:
    configText = content_file.readlines()

strFinal=""
strFinal=strFinal+roundingModesEncoding+AbsoluteValueFunctionEncoding

i=0

while i<len(configText):
	lineConfig=' '.join(configText[i].split())
	if lineConfig=="":
		i=i+1
	elif "%" in lineConfig:
		i=i+1
	elif lineConfig.startswith("Float:"):
		variablesFP,precisionFP=buildVariablesFromConfig(lineConfig)
		for var in variablesFP:
			strFinal=strFinal+encodeNewVariable(var,True)
		i=i+1
	elif lineConfig.startswith("Real:"):
		variablesReal,discardPrecisionForReals=buildVariablesFromConfig(lineConfig)
		strFinal=strFinal+encodeRealVariables(variablesReal)
		i=i+1
	else:
		lineConfig=lineConfig.replace("\n","")
		if "And" in lineConfig or "and" in lineConfig:
			conds=encodeAndCondition(lineConfig)
			for cond in conds:
				configText.append(cond)
			i=i+1
		elif "Or" in lineConfig or "or" in lineConfig:
			resultAssertion,conds,parenthesis=encodeOrCondition(lineConfig)
			for cond in conds:
				tmpEnconding,assertion=encodeLineInterface(cond,variablesFP,precisionFP,variablesReal,smtRoundingMode,initiateTempVarForArithmeticOperation)
				strFinal=strFinal+tmpEnconding+"\n"
				resultAssertion=resultAssertion+assertion+" "
			resultAssertion=resultAssertion[:-1]
			resultAssertion=resultAssertion+parenthesis
			strFinal=strFinal+resultAssertion+"\n"
			i=i+1
		elif "Not" in lineConfig or "not" in lineConfig:
			resultAssertion,cond,parenthesis=encodeNotCondition(lineConfig)
			tmpEncoding,assertion=encodeLineInterface(cond,variablesFP,precisionFP,variablesReal,smtRoundingMode,initiateTempVarForArithmeticOperation)
			resultAssertion=resultAssertion+assertion+" ) ) \n"
			strFinal=strFinal+tmpEncoding+resultAssertion
			i=i+1
		else:
			tmpEconding,assertion=encodeLineInterface(lineConfig,variablesFP,precisionFP,variablesReal,smtRoundingMode,initiateTempVarForArithmeticOperation)
			strFinal=strFinal+tmpEconding+"\n"+"( assert "+assertion+" )\n\n"
			i=i+1

strFinal=strFinal+"\n(check-sat)\n(get-model)"

if ActivateBinarySearch=="True":
	prop="Binary"
else:
	prop="Linear"

File=open("smtlib2"+prop+"SearchAssignment.txt","w+")
File.write(strFinal)
File.close()
print "\n\nDONE"



