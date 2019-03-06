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
import bigfloat
from ToSinglePrecisionConstants import *

def DAbs(a):
	if a>Decimal(0):
		return a
	else:
		return -a

def setContextForRoundingMode(smtRoundingMode):
	if smtRoundingMode=="rnd-to-zero":
		bigfloat.setcontext(bigfloat.RoundTowardZero)
		decimal.getcontext().rounding= ROUND_DOWN #(towards zero),
	elif smtRoundingMode=="rnd-to-positive":
		bigfloat.setcontext(bigfloat.RoundTowardPositive)
		decimal.getcontext().rounding= ROUND_CEILING #(towards Infinity)
	elif smtRoundingMode=="rnd-to-negative":
		bigfloat.setcontext(bigfloat.RoundTowardNegative)
		decimal.getcontext().rounding= ROUND_FLOOR #(towards -Infinity),
	elif smtRoundingMode=="rnd-to-nearest-away":
		bigfloat.setcontext(bigfloat.RoundAwayFromZero)
		decimal.getcontext().rounding= ROUND_HALF_UP #(to nearest with ties going away from zero)
	elif smtRoundingMode=="rnd-to-nearest-even":
		bigfloat.setcontext(bigfloat.RoundTiesToEven)
		decimal.getcontext().rounding= ROUND_HALF_EVEN #(to nearest with ties going to nearest even integer)


def defineRoundingModes():
	roundingModes=dict()
	roundingModes["rnd-to-negative"]="(define-fun rnd-to-negative ((x Real)) Int (to_int x))"
	roundingModes["ceil"]="(define-fun ceil ((x Real)) Int (ite (= x (to_int x)) (to_int x) (+ 1 (to_int x))))"
	roundingModes["rnd-to-positive"]=roundingModes["ceil"]+"\n"+"(define-fun rnd-to-positive ((x Real)) Int (ceil x))"
	roundingModes["rnd-to-zero"]=roundingModes["rnd-to-positive"]+"\n"+roundingModes["rnd-to-negative"]+"\n"+"(define-fun rnd-to-zero ((x Real)) Int (ite (> x 0.0) (rnd-to-negative x) (rnd-to-positive x)))"
	roundingModes["rnd-to-nearest-away"]="(define-fun rnd-to-nearest-away ((x Real)) Int (to_int (+ x 0.5)))"
	roundingModes["iseven"]="(define-fun iseven ((x Int)) Bool (ite (= 0 (mod x 2)) true false))"
	roundingModes["rnd-to-nearest-even"]=roundingModes["iseven"]+"\n"+"(define-fun rnd-to-nearest-even ((x Real)) Int (let ((y (ceil (- x 0.5))) (z (to_int (+ x 0.5)))) (ite (= y z) y (ite (iseven y) y z))))"
	return roundingModes

def computePowers(minVal,maxVal):
	res=[]
	tmpValue=int(Decimal(Decimal(maxVal).log10()/Decimal(2).log10()))
	tmpExp=tmpValue
	tmpValue=Decimal(2**(tmpExp))
	while tmpValue>minVal:
		res.append(tmpExp)
		tmpExp=tmpExp-1
		tmpValue=Decimal(2**(tmpExp))
	res.append(tmpExp)
	return res[::-1]


def getAbsLowerBound(bound):
	vals=bound.split(",")
	absVals=[Decimal(number) for number in vals]
	minVal=min(absVals)
	return max(minVal,Decimal(0.0))

def getAbsUpperBound(bound):
	vals=bound.split(",")
	absVals=[Decimal(number) for number in vals]
	absVals=map(abs, absVals)
	return max(absVals)

def getUpperBound(bound):
	return Decimal(eval(bound.split(",")[1]))

def getLowerBound(bound):
	return Decimal(eval(bound.split(",")[0]))

def getRoundingValue(bound):
	return bound.split(",")[1]

#return the name of the variable
def getNameFromVar(var):
	tmp=var.split("=")[0]
	tmp=tmp.split("[")[0]
	return tmp

def strFormatFromDecimal(num):
	tmp='{:f}'.format(num)
	if "." in tmp:
		return tmp
	else:
		return tmp+".0"

#(>,<,>=,<=,==,!=)
def getLogicComparator(lineConfig):
	if ">=" in lineConfig:
		tmp=lineConfig.split(">=")
		return "(>=",tmp[0], tmp[1],")"
	if "<=" in lineConfig:
		tmp=lineConfig.split("<=")
		return "(<=", tmp[0], tmp[1],")"
	if "!=" in lineConfig:
		tmp=lineConfig.split("!=")
		return "(not (=",tmp[0], tmp[1],"))"
	if "=" in lineConfig:
		tmp=lineConfig.split("=")
		return "(=",tmp[0], tmp[1], ")"
	if ">" in lineConfig:
		tmp=lineConfig.split(">")
		return "(>", tmp[0], tmp[1], ")"
	if "<" in lineConfig:
		tmp=lineConfig.split("<")
		return "(<", tmp[0], tmp[1], ")"
	return "","","",""

def containsAny(chars, val):
    for c in chars:
        if c in val:
					return c
    return ""

def checkIsANumber(operandRight):
	try:
		Decimal(eval(operandRight))
		return True
	except:
		return False

def doWeNeedTempVar(cond):
	if "+FP" in cond:
		return True
	if "-FP" in cond:
		return True
	if "*FP" in cond:
		return True
	if "\FP" in cond:
		return True
	return False

def buildLeftOperand(operand,variablesFP,variablesReal):
	tmp=operand.replace(" ","")
	tmp=tmp.replace("\n","")
	tmp=tmp.replace("(","")
	tmp=tmp.replace(")","")
	retValue=tmp
	mathOper=""
	if "-FP" in operand or "-" in operand:
		retValue=retValue.replace("-FP","")
		retValue=retValue.replace("-","")
		if retValue in variablesFP:
			mathOper="FP"
		if retValue in variablesReal:
			mathOper="R"
		retValue="(- 0 "+retValue+")"
		return retValue,mathOper
	else:
		if retValue in variablesFP:
			mathOper="FP"
		if retValue in variablesReal:
			mathOper="R"
		return retValue,mathOper
	return "", ""

def buildRightExpressionConstant(leftOperand,operation,variablesFP,precisionFP,variablesReal):
	operandRight=operation.replace(" ","")
	operandRight=operandRight.replace("\n","")
	operandRight=operandRight.replace(")","")
	operandRight=operandRight.replace("(","")
	result=""
	parentesi=""
	if checkIsANumber(operandRight):
		if operandRight.startswith("-"):
			operandRight=operandRight[1:]
			result="(- 0 "
			parentesi=")"
		if leftOperand in precisionFP:
			precisionL=precisionFP[leftOperand][0]
			if precisionL == 23:#single precision
				constStr=strFormatFromDecimal(single(eval(operandRight)))
			elif precisionL == 52:#double precision
				constStr=strFormatFromDecimal(Decimal(eval(operandRight)))
			else:
				exit("Custom Precision not yet implemented")
		elif leftOperand in variablesReal:
			constStr=strFormatFromDecimal(Decimal(operandRight))
		else:
			exit("Left Operand not found")
		result=result+constStr+parentesi
	return result

def buildRightVariable(operation,variablesFP,variablesReal):
	operandRight=str(operation)
	operandRight=operandRight.replace(" ","")
	operandRight=operandRight.replace("\n","")
	absExists=False
	if "abs" in operation:
		absExists=True
		operandRight=operandRight.replace("abs","")
		operandRight=operandRight.replace("(","")
		operandRight=operandRight.replace(")","")
	mathOper=""
	c=containsAny("+-",operandRight)
	if not c =="":
		operands=operandRight.split(c)
	else:
		operands=list()
		operands.append(operandRight)
	if len(filter(None, operands))==1:
		tmp=filter(None, operands)[0]
		if tmp in variablesFP:
			mathOper="FP"
		if tmp in variablesReal:
			mathOper="R"
		retValue=""
		parentesi=""
		if c == '-':
			retValue="(- 0 "
			parentesi=")"
		if absExists:
			retValue="(myabs "+retValue
			parentesi=parentesi+")"
		retValue=retValue+tmp+parentesi
		return retValue,mathOper
	return "",""

def buildRightExpressionOperation(operation,variablesFP,precisionFP,variablesReal):
	operandRight=str(operation)
	operandRight=operandRight.replace(" ","")
	operandRight=operandRight.replace("\n","")
	absExists=False
	if "abs" in operandRight:
		absExists=True
		operandRight=operandRight.replace("abs","")
		operandRight=operandRight.replace("(","")
		operandRight=operandRight.replace(")","")
	c=containsAny("+-*/",operandRight)
	if not c == "":
		operands=operandRight.split(c)
	else:
		operands=operandRight
	if len(filter(None, operands))==2:
		op1=(filter(None, operands)[0]).replace("FP","")
		op2=(filter(None, operands)[1]).replace("FP","")
		if ((op1 in variablesFP) or (op1 in variablesReal)) and ((op2 in variablesFP) or (op2 in variablesReal)):
			if (c+"FP") in operandRight:
				retValue="(" +c
				parentesi=")"
				if absExists:
					retValue="(myabs "+retValue
					parentesi=parentesi+")"
				retValue=retValue+" "+op1+" "+op2+parentesi

				if (precisionFP[op1][0]==52 and precisionFP[op1][1]==11) or (precisionFP[op2][0]==52 and precisionFP[op2][1]==11):
					precOP="double"
				elif (precisionFP[op1][0]==23 and precisionFP[op1][1]==8) and (precisionFP[op2][0]==23 and precisionFP[op2][1]==8):
					precOP="single"
				else:
					return "","",""
				return retValue,"FP",precOP
			else:
				retValue="(" +c
				parentesi=")"
				if absExists:
					retValue="(myabs "+retValue
					parentesi=parentesi+")"
				retValue=retValue+" "+op1+" "+op2+parentesi
				return retValue,"R","real"
		else:
			return "","",""
	else:
		return "","",""

def encodeConstantProblem(leftOperator,symbol,constant,endingParenthesis):
	return symbol+" "+leftOperator+" "+constant+" "+endingParenthesis

def encodeVariableProblem(leftOperator,symbol,variable,endingParenthesis):
	return symbol+" "+leftOperator+" "+variable+" "+endingParenthesis

def encodeLineInterface(lineConfig,variablesFP,precisionFP,variablesReal,smtRoundingMode,initiateTempVarForArithmeticOperation):
	assertion,symbol,operation,precOp,leftArithmetic,rightAritmeticOperation,endingParenthesis,TMPsmtRoundingMode=encodeLine(lineConfig,variablesFP,precisionFP,variablesReal,smtRoundingMode)
	if symbol=="" and operation=="":
		return "",assertion
	else:
		leftOperator=assertion
		tmpOperation=operation.replace(" ","")
		tmpOperation=tmpOperation.replace("(","")
		tmpOperation=tmpOperation.replace(")","")
		tempVar="temp"+tmpOperation
		tmpEnconding=""
		if not tempVar in variablesFP:
			tmpEnconding=initiateTempVarForArithmeticOperation(tempVar,operation,precOp)
		assertion=encodeArithmeticProblem(leftOperator,tempVar,symbol,"",leftArithmetic,rightAritmeticOperation,endingParenthesis,smtRoundingMode)
		return tmpEnconding,assertion

def encodeArithmeticProblem(leftOperator,tempVar,symbol,operation,leftArithmetic,rightAritmetic,endingParenthesis,smtRoundingMode):
	#if leftArithmetic=="R" and rightAritmetic=="FP":
	#	exit("Left operand is Real and right operand is Float")
	# Note. You can assign a FP computation to a Real variable.

	if leftArithmetic=="FP" and rightAritmetic=="R":
		exit("Error. Left operand is FP and right operand is Real")
	if leftArithmetic=="R":
		return symbol+" "+leftOperator+" "+operation+" "+endingParenthesis
	else:
		return symbol+" (* two-to-exp-p-minus-e-"+str(tempVar)+" "+str(leftOperator)+") (to_real ("+smtRoundingMode+" (* "+tempVar+" two-to-exp-p-minus-e-"+str(tempVar)+"))))"

def getPrecisionFromVar(var):
	myVar=var
	if "=" in var:
		myVar=var.split("=")[0]

	if "[" in myVar:
		myVar=myVar.split("[")[1]
		myVar=myVar.split("]")[0]
		formatP=myVar
	else:
		formatP="DOUBLE"

	if formatP.upper()=="SINGLE":
		exponent=singleExponentPrecision
		mantissa=singleMantissaPrecision
	elif formatP.upper()=="DOUBLE":
		exponent=doubleExponentPrecision
		mantissa=doubleMantissaPrecision
	else:#to do custom precision
		exit("Precision variables missing ex. NameVar[single]=[0;1] or NameVar[double]=[0;1]")
	return mantissa,exponent

def adjustBoundsForFloats(bound,direction,precision):
	if not "." in bound:
		if "E" in bound:
			bounds=bound.split("E")
			bound=bounds[0]+".0E"+bounds[1]
		else:
			bound=bound+".0"
	newRes=bound

	if direction=="+":
		newRes=next111(bound,precision)
	if direction=="-":
		newRes=previous111(bound,precision)
	return newRes

def encodeDomainAndRanges(var,rangeFP,precisionFP):
	resLower,resUpper,orZero=buildBoundsForSMT(rangeFP)

	mantissaPrecision=precisionFP[0]
	exponentPrecision=precisionFP[1]

	currentTwoPowerMantissa=strFormatFromDecimal(Decimal(2**mantissaPrecision))

	valueSmallestFloat=Decimal(2**(-mantissaPrecision)*(2**-(2**(exponentPrecision-1)-1-1)))
	strSmallestFloat=strFormatFromDecimal(valueSmallestFloat)

	valueBiggestFloat=Decimal((2-(2**-mantissaPrecision))*2**(2**(exponentPrecision-1)-1))

	strBiggestFloat=strFormatFromDecimal(valueBiggestFloat)

	if orZero:
		dominioRangeVar="or ( and (>= abs-"+str(var)+" "+strSmallestFloat+") (<= abs-"+str(var)+" "+resUpper+")) (= abs-"+str(var)+" 0.0)"
	else:
		positiveBounds=rangeFP
		positiveLB=Decimal(DAbs(eval(positiveBounds.split(",")[0])))
		positiveUB=Decimal(DAbs(eval(positiveBounds.split(",")[1])))

		strPositiveLB=strFormatFromDecimal(min(positiveLB,positiveUB))
		strPositiveUB=strFormatFromDecimal(max(positiveLB,positiveUB))
		dominioRangeVar="and (>= abs-"+str(var)+" "+strPositiveLB+") (<= abs-"+str(var)+" "+strPositiveUB+")"

	encodingCurrentVar="(assert ("+dominioRangeVar+"))\n"

	if orZero:
		currentRangeVar="xor ( and (>= "+str(var)+" "+strSmallestFloat+") (<= "+str(var)+" "+resUpper+")) (= "+str(var)+" 0.0) ( and (<= "+str(var)+" (- 0 "+strSmallestFloat+")) (>= "+str(var)+" "+resLower+"))"
	else:
		currentRangeVar="and (>= "+str(var)+" "+resLower+") (<= "+str(var)+" "+resUpper+")"

	encodingCurrentVar=encodingCurrentVar+"(assert ("+currentRangeVar+"))\n"
	# encodingCurrentVar=encodingCurrentVar+"(assert (=> (= 0.0 abs-"+str(var)+") (= two-to-exp-p-minus-e-"+str(var)+" "+currentTwoPowerMantissa+" )))\n\n"
	return encodingCurrentVar

def buildVariablesFromConfig(lineConfig):
	myVars=lineConfig.split(":")[1]
	myVars=myVars.replace(" ","")
	myVars=myVars.replace("\n","")
	singleVars=myVars.split(",")
	variables=dict()
	precision=dict()
	for var in singleVars:
		if not var == "":
			res=getBoundFromVar(var)
			upperStr=res.split(",")[1]
			lowerStr=res.split(",")[0]
			if "Float" in lineConfig:
				mantissa,exponent=getPrecisionFromVar(var)
				precision[getNameFromVar(var)]=(int(mantissa),int(exponent))

				if "+Infinity" in upperStr:
					biggestFloat=Decimal((2-(2**-mantissa))*2**(2**(exponent-1)-1))
					upperStr=upperStr.replace("+Infinity",strFormatFromDecimal(biggestFloat))
				else:
					upperStr=upperStr.replace(upperStr,adjustBoundsForFloats(upperStr,"+",precision[getNameFromVar(var)]))

				if "-Infinity" in lowerStr:
					negbiggestFloat=Decimal(-(2-(2**-mantissa))*2**(2**(exponent-1)-1))
					lowerStr=lowerStr.replace("-Infinity",strFormatFromDecimal(negbiggestFloat))
				else:
					lowerStr=lowerStr.replace(lowerStr,adjustBoundsForFloats(lowerStr,"-",precision[getNameFromVar(var)]))

				variables[getNameFromVar(var)]=lowerStr+","+upperStr
			elif "Real" in lineConfig:
				variables[getNameFromVar(var)]=res
			else:
				exit("Illegal string in variables declaration")
	return variables,precision

def buildTempOperation(nameVar,leftOperandName,precisionOP):
	mantissa,exponent=getPrecisionFromVar(leftOperandName)
	biggestFloat=Decimal(2-(getcontext().power(2,-mantissa)))*Decimal(getcontext().power(2,(getcontext().power(2,exponent-1)-1)))
	variablesFP[nameVar]=""+strFormatFromDecimal(-biggestFloat)+","+strFormatFromDecimal(biggestFloat)


def encodeRealVariables(variablesReal):
	retStr=""
	for realVar in variablesReal:
		bound=variablesReal[realVar]
		smtRealVar="(declare-const "+str(realVar)+" Real)\n"
		resLower,resUpper,zeroUselessInReals=buildBoundsForSMT(bound)
		if not "Infinity" in resUpper:
			smtRealVar=smtRealVar+"(assert (<= "+str(realVar)+" "+resUpper+"))\n"
		if not "Infinity" in resLower:
			smtRealVar=smtRealVar+"(assert (>= "+str(realVar)+" "+resLower+"))\n"
		retStr=retStr+smtRealVar+"\n\n"
	return retStr

def buildBoundsForSMT(bound):

	tmpBounds=bound.split(",")

	if "+Infinity" in tmpBounds[1]:
		decimalUB=Decimal("+Infinity")
	elif "-Infinity" in tmpBounds[1]:
		decimalUB=Decimal("-Infinity")
	else:
		decimalUB=getUpperBound(bound)

	if "+Infinity" in tmpBounds[0]:
		decimalLB=Decimal("+Infinity")
	elif "-Infinity" in tmpBounds[0]:
		decimalLB=Decimal("-Infinity")
	else:
		decimalLB=getLowerBound(bound)

	zero=Decimal(0.0)

	if decimalUB<decimalLB:
		exit("Range of variables problem")

	orZero=False
	if zero>=decimalLB and zero<=decimalUB:
		orZero=True

	resUpper=strFormatFromDecimal(decimalUB)
	resLower=strFormatFromDecimal(decimalLB)

	if (decimalUB != Decimal("-Infinity")):
		if (decimalUB<zero):
			resUpper=resUpper.replace("-","")
			resUpper="(- 0 "+resUpper+")"
	if (decimalLB != Decimal("-Infinity")):
		if (decimalLB<zero):
			resLower=resLower.replace("-","")
			resLower="(- 0 "+resLower+")"
	return resLower,resUpper,orZero

#given a bound in the form [2;3] returns 2,3
def getBoundFromVar(var):
	if "=" in var:
		myVar=var.split("=")[1]
		myVar=myVar.replace(";",",")
		myVar=myVar.replace("[","")
		myVar=myVar.replace("]","")
		myVar=myVar.upper()
	else:
		myVar="-Infinity,+Infinity"
	return myVar

def encodeAndCondition(lineConfig):
	conds=lineConfig.replace("And(","")
	conds=conds.replace("and(","")
	while conds[-1]==" ":
		conds=conds[:-1]
	conds=conds[:-1]
	conds=conds.split(",")
	return conds

def encodeNotCondition(lineConfig):
	cond=lineConfig.replace("Not(","")
	cond=lineConfig.replace("not(","")
	while cond[-1]==" ":
		cond=cond[:-1]
	resultAssertion= "( assert ( not "
	parenthesis=" ) ) \n\n"
	return resultAssertion,cond,parenthesis

def encodeOrCondition(lineConfig):
	conds=lineConfig.replace("Or(","")
	conds=conds.replace("or(","")
	while conds[-1]==" ":
		conds=conds[:-1]
	conds=conds[:-1]
	resultAssertion= "( assert ( or "
	conds=conds.split(",")
	parenthesis=" ) ) \n\n"
	return resultAssertion,conds,parenthesis

def encodeLine(lineConfig,variablesFP,precisionFP,variablesReal,smtRoundingMode):
	symbol,leftOperatorDirty,rightOperationDirty,endingParenthesis=getLogicComparator(lineConfig)
	leftOperator,leftArithmetic=buildLeftOperand(leftOperatorDirty,variablesFP,variablesReal)
	constant=buildRightExpressionConstant(leftOperator,rightOperationDirty,variablesFP,precisionFP,variablesReal)
	variable,rightAritmeticVariable=buildRightVariable(rightOperationDirty,variablesFP,variablesReal)
	operation,rightAritmeticOperation,precOp=buildRightExpressionOperation(rightOperationDirty,variablesFP,precisionFP,variablesReal)

	if (leftOperator!="" and leftArithmetic!=""):
		if (symbol!=""):
			if constant!="":
				assertion=encodeConstantProblem(leftOperator,symbol,constant,endingParenthesis)
			elif variable!="" and rightAritmeticVariable!="":
				assertion=encodeVariableProblem(leftOperator,symbol,variable,endingParenthesis)
			elif operation!="" and rightAritmeticOperation!="" and precOp!="":
				if rightAritmeticOperation=="R":
					assertion=encodeArithmeticProblem(leftOperator,"",symbol,operation,leftArithmetic,rightAritmeticOperation,endingParenthesis,smtRoundingMode)
				else:
					return leftOperator,symbol,operation,precOp,leftArithmetic,rightAritmeticOperation,endingParenthesis,smtRoundingMode
			else:
				exit("Problem with the right part of the expression")
		else:
			exit("Comparator =,>=,etc problem")
	else:
		exit("Left operand problem")
	return assertion,"","","","","","",""

singleMantissaPrecision=23
singleExponentPrecision=8
doubleMantissaPrecision=52
doubleExponentPrecision=11
