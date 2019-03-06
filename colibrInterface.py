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

import sys,os
sys.path.insert(0, os.getcwd()+"/preciseRealizer/")
sys.path.insert(0, "/fprock/preciseRealizer")

print "The current script directory: "
script_dir = os.path.dirname(sys.argv[0])
if script_dir == "":
    script_dir = "./"
print script_dir
print "Current working directory: "
cwd_dir = os.getcwd()
print cwd_dir
resultFolder= cwd_dir + "/results/"

thepath = script_dir + "../library"
print thepath

from library import *

def negateSymbol(line):
	if "$=<" in line:
		return "$=<","$>"
	if "$>=" in line:
		return "$>=","$<"
	if "$=" in line:
		return "$=","$\="
	if "$\=" in line:
		return "$\=","$="
	if "$>" in line:
		return "$>","$=<"
	if "$<" in line:
		return "$<","$>="

def fromDiscreteToReal(var):
	if var in precisionFP and precisionFP[var]==(23,8):
		return "real_from_float("+var+")"
	if var in precisionFP and precisionFP[var]==(52,11):
		return "real_from_double("+var+")"
	if not var in precisionFP:
		return var

def encodeAndOrNotConditionColibri(opt1,opt2,lineConfig):
	conds=lineConfig.replace(opt1,"")
	conds=conds.replace(opt2,"")
	while conds[-1]==" ":
		conds=conds[:-1]
	conds=conds[:-1]
	conds=conds.split(",")
	return conds

def cleanStrSpace(val):
	return val.replace(" ","")

def getUpperBound(bound):
	return bound.split(",")[1]

def getLowerBound(bound):
	return bound.split(",")[0]

def getLogicComparatorColibri(lineConfig):
	if ">=" in lineConfig:
		tmp=lineConfig.split(">=")
		return ">=","$>=",tmp[0], tmp[1]
	if "<=" in lineConfig:
		tmp=lineConfig.split("<=")
		return "<=","$=<", tmp[0], tmp[1]
	if "!=" in lineConfig:
		tmp=lineConfig.split("!=")
		return "!=","$\=",tmp[0], tmp[1]
	if "=" in lineConfig:
		tmp=lineConfig.split("=")
		return "=","$=",tmp[0], tmp[1]
	if ">" in lineConfig:
		tmp=lineConfig.split(">")
		return ">","$>",tmp[0], tmp[1]
	if "<" in lineConfig:
		tmp=lineConfig.split("<")
		return "<","$<", tmp[0], tmp[1]
	return "","","",""

def getOperatorColibri(lineConfig):
	if "+" in lineConfig:
		if "+FP" in lineConfig:
			tmp=lineConfig.split("+FP")
			return "+FP",tmp[0], tmp[1]
		tmp=lineConfig.split("+")
		return "+",tmp[0], tmp[1]
	if "-" in lineConfig:
		if "-FP" in lineConfig:
			tmp=lineConfig.split("-FP")
			return "-FP",tmp[0], tmp[1]
		tmp=lineConfig.split("-")
		return "-",tmp[0], tmp[1]
	if "*" in lineConfig:
		if "*FP" in lineConfig:
			tmp=lineConfig.split("*FP")
			return "*FP",tmp[0], tmp[1]
		tmp=lineConfig.split("*")
		return "*",tmp[0], tmp[1]
	if "/" in lineConfig:
		if "/FP" in lineConfig:
			tmp=lineConfig.split("/FP")
			return "/FP",tmp[0], tmp[1]
		tmp=lineConfig.split("/")
		return "/",tmp[0], tmp[1]
	return "","",""


#given a bound in the form [2;3] returns 2,3
def getBoundFromVarColibri(var):
	if "=" in var:
		myVar=var.split("=")[1]
		myVar=myVar.replace(";",",")
		myVar=myVar.replace("[","")
		myVar=myVar.replace("]","")
	else:
		myVar="-1.0Inf,1.0Inf"
	return myVar

def adjustBoundsForFloatsColibri(res,precVar):
	boundsTmp=res.split(",")
	lBound=boundsTmp[0]
	uBound=boundsTmp[1]

	lBound=lBound.replace("+Infinity","1.0Inf")
	lBound=lBound.replace("-Infinity","-1.0Inf")

	uBound=uBound.replace("+Infinity","1.0Inf")
	uBound=uBound.replace("-Infinity","-1.0Inf")

	if not "Inf" in lBound:
		tmp=lBound.upper()
		if not "E" in tmp:
			if not "." in lBound:
				lBound=lBound+".0"
	if not "Inf" in uBound:
		tmp=uBound.upper()
		if not "E" in tmp:
			if not "." in uBound:
				uBound=uBound+".0"

	newRes=""

	if (not "Inf" in lBound):# and strFormatFromDecimal(Decimal(eval(lBound)))!=lBound ):
		newRes=previous111(lBound,precVar)+","
	else:
		newRes=lBound+","
	if (not "Inf" in uBound):# and strFormatFromDecimal(Decimal(eval(uBound)))!=uBound):
		newRes=newRes+next111(uBound,precVar)
	else:
		newRes=newRes+uBound
	return newRes

def buildVariablesFromConfigColibri(lineConfig):
	myVars=lineConfig.split(":")[1]
	myVars=myVars.replace(" ","")
	myVars=myVars.replace("\n","")
	singleVars=myVars.split(",")
	variables=dict()
	precision=dict()
	for var in singleVars:
		if not var == "":
			res=getBoundFromVarColibri(var)
			if "Float" in lineConfig:
				mantissa,exponent=getPrecisionFromVar(var)
				precision[getNameFromVar(var)]=(int(mantissa),int(exponent))
				newRes=adjustBoundsForFloatsColibri(res,precision[getNameFromVar(var)])
				variables[getNameFromVar(var)]=newRes
			elif "Real" in lineConfig:
				variables[getNameFromVar(var)]=res
			else:
				exit("Illegal string in variables declaration")
	return variables,precision

def encodeLineColibri(lineConfig):
	tmpConfig=str(lineConfig)
	tmpConfig=tmpConfig.replace("\n","")

	symbol,newSymbol,leftOperandDirty,rightOperationDirty=getLogicComparatorColibri(tmpConfig)

	absExist=False

	if "abs(" in rightOperationDirty:
		absExist=True
		rightOperationDirty=rightOperationDirty.replace("abs(","")
		rightOperationDirty=rightOperationDirty.replace(")","")

	operation,operand1,operand2=getOperatorColibri(rightOperationDirty)

	if checkIsANumber(rightOperationDirty):
		operand1=" "+rightOperationDirty
		operand2=""

	if "FP" in operation:
		tmpConfig=tmpConfig.replace("FP","")

	tmpConfig=tmpConfig.replace(symbol,newSymbol)
	if operand1!="" and operand2!="":

		leftOperand=cleanStrSpace(leftOperandDirty)
		operand1=cleanStrSpace(operand1)
		operand2=cleanStrSpace(operand2)

		if not leftOperand in precisionFP and not operand1 in precisionFP and not operand2 in precisionFP:
			pass #all reals
		elif leftOperand in precisionFP and operand1 in precisionFP and operand2 in precisionFP and precisionFP[leftOperand]==(23,8) and precisionFP[operand1]==(23,8) and precisionFP[operand2]==(23,8):
			pass #all single
		elif leftOperand in precisionFP and operand1 in precisionFP and operand2 in precisionFP and precisionFP[leftOperand]==(52,11) and precisionFP[operand1]==(52,11) and precisionFP[operand2]==(52,11):
			pass #all double
		else:
			newleftOperand=fromDiscreteToReal(leftOperand)
			newoperand1=fromDiscreteToReal(operand1)
			newoperand2=fromDiscreteToReal(operand2)

			if absExist:
				tmpConfig=newleftOperand+" "+newSymbol+" abs("+newoperand1+ " "+operation+" "+ newoperand2+")"
			else:
				tmpConfig=newleftOperand+" "+newSymbol+" "+newoperand1+ " "+operation+" "+newoperand2

	elif operand1=="" and operand2=="":
		newleftOperand=cleanStrSpace(leftOperandDirty)
		newrightOperation=cleanStrSpace(rightOperationDirty)

		if not checkIsANumber(newrightOperation):
			newleftOperand=fromDiscreteToReal(newleftOperand)
			newrightOperation=fromDiscreteToReal(newrightOperation)

		tmpConfig=tmpConfig.replace(leftOperandDirty,newleftOperand)
		tmpConfig=tmpConfig.replace(rightOperationDirty,newrightOperation)
	elif operand1!="" and operand2=="":
		newleftOperand=cleanStrSpace(leftOperandDirty)
		newoperand1=cleanStrSpace(operand1)

		if not checkIsANumber(operand1):
			newleftOperand=fromDiscreteToReal(newleftOperand)
			newoperand1=fromDiscreteToReal(newoperand1)

		tmpConfig=tmpConfig.replace(leftOperandDirty,newleftOperand)
		tmpConfig=tmpConfig.replace(operand1,newoperand1)
	elif operand1=="" and operand2!="":
		newleftOperand=cleanStrSpace(leftOperandDirty)
		newoperand2=cleanStrSpace(operand2)

		if not checkIsANumber(newoperand2):
			newleftOperand=fromDiscreteToReal(leftOperand)
			newoperand2=fromDiscreteToReal(newoperand2)

		tmpConfig=tmpConfig.replace(leftOperandDirty,newleftOperand)
		tmpConfig=tmpConfig.replace(operand2,newoperand2)
	else:
		exit("Not recognized")
	return tmpConfig

nameFile=str("config.txt") #name of the config file
with open(nameFile,"r+") as content_file:
    configText = content_file.readlines()

i=0
strFinal="%\n"
while i<len(configText):
	lineConfig=' '.join(configText[i].split())
	if lineConfig=="":
		i=i+1
	elif "%" in lineConfig:
		i=i+1
	elif lineConfig.startswith("Float:"):
		variablesFP,precisionFP=buildVariablesFromConfigColibri(lineConfig)

		labelVariablesSingle=[]
		labelVariablesDouble=[]
		for var in precisionFP:
			if precisionFP[var]==(23,8):
				labelVariablesSingle.append(var)
			if precisionFP[var]==(52,11):
				labelVariablesDouble.append(var)

		strFinal=strFinal+"real_vars(float,["
		t=False
		for var in labelVariablesSingle:
			strFinal=strFinal+var+", "
			t=True
		if t:
			strFinal=strFinal[0:-2]
		strFinal=strFinal+"]),\n"

		strFinal=strFinal+"real_vars(double,["
		t=False
		for var in labelVariablesDouble:
			strFinal=strFinal+var+", "
			t=True
		if t:
			strFinal=strFinal[0:-2]
		strFinal=strFinal+"]),\n"

		for var in labelVariablesSingle:
			bound=variablesFP[var]
			resUpper=getUpperBound(bound)
			resLower=getLowerBound(bound)
			#resUpper=strFormatFromDecimal(decUpper)
			#resLower=strFormatFromDecimal(decLower)
			#X $: -1.0 .. +1.0,
			varEncode=var+ " $: "+resLower+" .. "+ resUpper+",\n"
			strFinal=strFinal+varEncode

		for var in labelVariablesDouble:
			bound=variablesFP[var]
			resUpper=getUpperBound(bound)
			resLower=getLowerBound(bound)
			#resUpper=strFormatFromDecimal(decUpper)
			#resLower=strFormatFromDecimal(decLower)
			#X $: -1.0 .. +1.0,
			varEncode=var+ " $: "+resLower+" .. "+ resUpper+",\n"
			strFinal=strFinal+varEncode
		i=i+1

	elif lineConfig.startswith("Real:"):
		variablesReal,discardPrecisionForReals=buildVariablesFromConfigColibri(lineConfig)
		strFinal=strFinal+"real_vars(real,["
		t=False
		for var in variablesReal:
			strFinal=strFinal+var+", "
			t=True
		if t:
			strFinal=strFinal[0:-2]
		strFinal=strFinal+"]),\n"
		for var in variablesReal:
			bound=variablesReal[var]
			resUpper=getUpperBound(bound)
			resLower=getLowerBound(bound)
			#resUpper=strFormatFromDecimal(decUpper)
			#resLower=strFormatFromDecimal(decLower)
			#X $: -1.0 .. +1.0,
			varEncode=var+ " $: "+resLower+" .. "+ resUpper+",\n"
			strFinal=strFinal+varEncode
		i=i+1
	else:
		lineConfig=lineConfig.replace("\n","")
		if "And" in lineConfig or "and" in lineConfig:
			tmpConfig=str(lineConfig)
			conds=encodeAndOrNotConditionColibri("And(","and(",tmpConfig)
			result="and("
			for cond in conds:
				result=result+encodeLineColibri(cond)+", "
			result=result[:-2]+"),\n"
			strFinal=strFinal+result
			i=i+1
		elif "Or" in lineConfig or "or" in lineConfig:
			tmpConfig=str(lineConfig)
			conds=encodeAndOrNotConditionColibri("Or(","or(",tmpConfig)

			result="or("
			for cond in conds:
				result=result+encodeLineColibri(cond)+", "
			result=result[:-2]+"),\n"
			strFinal=strFinal+result
			i=i+1
		elif "not" in lineConfig or "Not" in lineConfig:
			tmpConfig=str(lineConfig)
			cond=encodeAndOrNotConditionColibri("Not(","not(",tmpConfig)[0]
			result=encodeLineColibri(cond)+",\n"
			symb,newSymb=negateSymbol(result)
			result=result.replace(symb,newSymb)
			strFinal=strFinal+result
			i=i+1
		else:
			tmpConfig=encodeLineColibri(lineConfig)
			strFinal=strFinal+tmpConfig+",\n"
			i=i+1

strFinal=strFinal[0:-2]
strFinal=strFinal+" . "
File=open(script_dir +"/smt_colibri.in","w+")
File.write(strFinal)
File.close()
print "\n\nDONE"


