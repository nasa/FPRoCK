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

import decimal
import math as _math
from decimal import *
import sys
import bigfloat

def strFormatFromDecimalLib(num):
	tmp='{:f}'.format(num)
	if "." in tmp:
		return tmp
	else:
		return tmp+".0"

def parse_bin(s):
	t = s.split('.')
	integer=t[0]
	fractional=t[1]
	integer=integer[::-1]
	val=Decimal(0.0)
	power=0
	for el in integer:
		val=val+(Decimal(el)*Decimal(2**power))
		power=power+1
	power=-1
	for el in fractional:
		val=val+(Decimal(el)*Decimal(2**power))
		power=power-1
	return val

def single(f):
	if _math.copysign(1.0, f) == 1.0:
			sign = 0
	else:
			sign = 1
	n, d = abs(f).as_integer_ratio()

	destinationPrecision=23
	doublePrecision=53

	k = d.bit_length() - 1

	check=str(bin(n))[2:]

	if len(check)<=destinationPrecision:
		k = d.bit_length() - 1
		return _dec_from_triple(sign, str(Decimal(n*(5**k))), -k)

	Nbin=bin(n)
	SBinN=Nbin
	Dbin=bin(d)

	maskUpper="0b"+str("1"*(destinationPrecision+1))
	maskUpper=maskUpper+str("0"*(len(str(SBinN))-len(maskUpper)))

	maskLower="0b"+str("0"*(destinationPrecision+1))
	queueLen=len(str(SBinN))-len(maskLower)
	maskLower=maskLower+str("1"*(len(str(SBinN))-len(maskLower)))

	upperPart=eval(SBinN)&eval(maskUpper)
	lowerPart=eval(SBinN)&eval(maskLower)

	upperPart=bin(upperPart)#format(upperPart, '053b')
	lowerPart=format(lowerPart, '0'+str(queueLen)+'b')

	upperPart=upperPart[2:destinationPrecision+3]

	integer=upperPart
	decimal=lowerPart
	tot=integer+"."+decimal

	res=Decimal(parse_bin(tot)).quantize(Decimal('1.'), rounding=	ROUND_HALF_EVEN)

	resBin= format(int(res), '0'+str(destinationPrecision)+'b')+"0"*(queueLen)

	newN=int(resBin,2)

	k = d.bit_length() - 1
	result = _dec_from_triple(sign, str(Decimal(newN*(5**k))), -k)

	return result

def _dec_from_triple(sign, coefficient, exponent, special=False):
	"""Create a decimal instance directly, without any validation,
	normalization (e.g. removal of leading zeros) or argument
	conversion.

	This function is for *internal use only*.
	"""

	self = object.__new__(Decimal)
	self._sign = sign
	self._int = coefficient
	self._exp = exponent
	self._is_special = special

	return self

"""
def previous(num):
	if _math.copysign(1.0, num) == 1.0:
			sign = 0
	else:
			sign = 1

	n, d = abs(num).as_integer_ratio()
	print n,d
	if n!=1 and d!=1:#if number num is not a power of two and it is not an integer
		n=n-1
	k = d.bit_length() - 1
	result = _dec_from_triple(sign, str(n*5**k), -k)
	return result

def nextone(num):
	if _math.copysign(1.0, num) == 1.0:
			sign = 0
	else:
			sign = 1

	n, d = abs(num).as_integer_ratio()
	print n,d
	if n!=1 and d!=1:#if number num is not a power of two and it is not an integer
		n=n+1
	k = d.bit_length() - 1
	result = _dec_from_triple(sign, str(n*5**k), -k)
	return result
"""

def previous111(strBound,precVar):
	if precVar==(23,8):
		print "single"
		origValue=single(eval(strBound))
		strOrigValue=strFormatFromDecimalLib(origValue)
		if strOrigValue!=strBound:#bound is not exactly representable in double or single precision
			n,d=bigfloat.next_down(eval(strOrigValue),context=bigfloat.precision(24)).as_integer_ratio()
			newValue=single(n/float(d))
			if newValue<origValue:
				return strFormatFromDecimalLib(newValue)
			else:
				exit("Problem in conversion of bound:"+strBound)
		else:
			return strOrigValue
	elif precVar==(52,11):
		origValue=Decimal(eval(strBound))
		strOrigValue=strFormatFromDecimalLib(origValue)
		if strOrigValue!=strBound:#bound is not exactly representable in double or single precision
			n,d=bigfloat.next_down(eval(strOrigValue),context=bigfloat.precision(53)).as_integer_ratio()
			newValue=eval("Decimal("+str(n)+"/"+str(d)+".0)")
			if newValue<origValue:
				return strFormatFromDecimalLib(newValue)
			else:
				exit("Problem in conversion of bound:"+strBound)
		else:
			return strOrigValue
	else:
		exit("Precision not recognized")

def next111(strBound,precVar):
	if precVar==(23,8):
		origValue=single(eval(strBound))
		strOrigValue=strFormatFromDecimalLib(origValue)
		if strOrigValue!=strBound:#bound is not exactly representable in double or single precision
			n,d=bigfloat.next_up(eval(strOrigValue),context=bigfloat.precision(24)).as_integer_ratio()
			newValue=single(n/float(d))
			if newValue>origValue:
				return strFormatFromDecimalLib(newValue)
			else:
				exit("Problem in conversion of bound:"+strBound)
		else:
			return strOrigValue
	elif precVar==(52,11):
		origValue=Decimal(eval(strBound))
		strOrigValue=strFormatFromDecimalLib(origValue)
		if strOrigValue!=strBound:#bound is not exactly representable in double or single precision
			n,d=bigfloat.next_up(eval(strOrigValue),context=bigfloat.precision(53)).as_integer_ratio()
			newValue=eval("Decimal("+str(n)+"/"+str(d)+".0)")
			if newValue>origValue:
				return strFormatFromDecimalLib(newValue)
			else:
				exit("Problem in conversion of bound:"+strBound)
		else:
			return strOrigValue
	else:
		exit("Precision not recognized")
#print parse_bin("0.0001100110011001100110011001100110011001100110011001100110011001100110011001100110011001101")
#print next111("-2.99999999999999",(23,8))
#print previous111("-2.99999999999999",(23,8))
#print next111("3.0",(52,11))
#print previous111("3.0",(52,11))
