#!/usr/bin/env python

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

import shlex
import subprocess
import os
import sys
import datetime
import signal
from threading import Timer

def mykill(procs):
	for proc in procs:
		try:
			print "KILL:" + str(os.getpgid(proc.pid))
			os.killpg(os.getpgid(proc.pid), signal.SIGKILL)  # Send the signal to all the process groups
		except:
			print "Process: "+str(proc.pid)+ " already died!"

if len(sys.argv)<4:
	print "Arg-1 Timeout in seconds \n"
	print "Arg-2 Rounding modes: rnd-to-zero, rnd-to-positive, rnd-to-negative, rnd-to-nearest-away, rnd-to-nearest-even\n"
	print "Arg-3 Name of the input file \n"
	exit("Please specify the 2 parameters. Ex. python executor.py 10 rnd-to-zero config.txt\n")
timeout=int(str(sys.argv[1]))
smtRoundingMode=str(sys.argv[2])
nameFile=str(sys.argv[3])

#config for Binary Search Numeric
print "The current script directory: "
script_dir = os.path.dirname(sys.argv[0])
if script_dir == "":
    script_dir = "./"
print script_dir
print "Current working directory: "
cwd_dir = os.getcwd()
print cwd_dir
resultFolder= cwd_dir + "/results/"
if not os.path.exists(resultFolder):
    os.makedirs(resultFolder)
exe0="python " + script_dir + "/preciseRealizer/solverBSN.py "+smtRoundingMode+" "+nameFile
print exe0
val0=os.system(exe0)
if val0==0:
	processes=[]
	print "Translation BSN succeed!"
	exeCVC4="cvc4 --quiet --produce-models --lang=smt2 ./smtlib2BinarySearchNumeric.txt"
	exez3="z3 ./smtlib2BinarySearchNumeric.txt"
	mathsat="mathsat ./smtlib2BinarySearchNumeric.txt"

	print exeCVC4
	exeCVC4=shlex.split(exeCVC4)
	with open(resultFolder+"cvc4BSN.txt","w+") as outcvc4:
		c=subprocess.Popen(exeCVC4,shell=False,preexec_fn=os.setsid,stdout=outcvc4,stderr=outcvc4)
	processes.append(c)

	print exez3
	exez3=shlex.split(exez3)
	with open(resultFolder+"z3BSN.txt","w+") as outz3:
		z=subprocess.Popen(exez3,shell=False,preexec_fn=os.setsid,stdout=outz3,stderr=outz3)
	processes.append(z)

	print mathsat
	mathsat=shlex.split(mathsat)
	with open(resultFolder+"mathsatBSN.txt","w+") as outmathsat:
		m=subprocess.Popen(mathsat,shell=False,preexec_fn=os.setsid,stdout=outmathsat,stderr=outmathsat)
	processes.append(m)

	#config for Binary Search Assignment
	exe1="python " + script_dir + "/preciseRealizer/solverBLSA.py "+smtRoundingMode+" "+nameFile+" "+str(True)
	print exe1
	val1=os.system(exe1)
	if val1==0:
		print "Translation BLSA succeed (Binary Assignment)!"
		exeCVC4="cvc4 --quiet --produce-models --lang=smt2 ./smtlib2BinarySearchAssignment.txt"
		exez3="z3 ./smtlib2BinarySearchAssignment.txt"
		mathsat="mathsat ./smtlib2BinarySearchAssignment.txt"

		print exeCVC4
		exeCVC4=shlex.split(exeCVC4)
		with open(resultFolder+"cvc4BSA.txt","w+") as outcvc4:
			c=subprocess.Popen(exeCVC4,shell=False,preexec_fn=os.setsid,stdout=outcvc4,stderr=outcvc4)
		processes.append(c)

		print exez3
		exez3=shlex.split(exez3)
		with open(resultFolder+"z3BSA.txt","w+") as outz3:
			z=subprocess.Popen(exez3,shell=False,preexec_fn=os.setsid,stdout=outz3,stderr=outz3)
		processes.append(z)

		print mathsat
		mathsat=shlex.split(mathsat)
		with open(resultFolder+"mathsatBSA.txt","w+") as outmathsat:
			m=subprocess.Popen(mathsat,shell=False,preexec_fn=os.setsid,stdout=outmathsat,stderr=outmathsat)
		processes.append(m)

		#config for Linear Search Assignment
		exe1BIS="python " + script_dir + "/preciseRealizer/solverBLSA.py "+smtRoundingMode+" "+nameFile+" "+str(False)
		print exe1BIS
		val1BIS=os.system(exe1BIS)
		if val1BIS==0:
			print "Translation BLSA succeed (Linear Assignment)!"
			exeCVC4="cvc4 --quiet --produce-models --lang=smt2 ./smtlib2LinearSearchAssignment.txt"
			exez3="z3 ./smtlib2LinearSearchAssignment.txt"
			mathsat="mathsat ./smtlib2LinearSearchAssignment.txt"

			print exeCVC4
			exeCVC4=shlex.split(exeCVC4)
			with open(resultFolder+"cvc4LSA.txt","w+") as outcvc4:
				c=subprocess.Popen(exeCVC4,shell=False,preexec_fn=os.setsid,stdout=outcvc4,stderr=outcvc4)
			processes.append(c)

			print exez3
			exez3=shlex.split(exez3)
			with open(resultFolder+"z3LSA.txt","w+") as outz3:
				z=subprocess.Popen(exez3,shell=False,preexec_fn=os.setsid,stdout=outz3,stderr=outz3)
			processes.append(z)

			print mathsat
			mathsat=shlex.split(mathsat)
			with open(resultFolder+"mathsatLSA.txt","w+") as outmathsat:
				m=subprocess.Popen(mathsat,shell=False,preexec_fn=os.setsid,stdout=outmathsat,stderr=outmathsat)
			processes.append(m)

			#config for COLIBRI
			exe2="python " + script_dir + "/colibri_2073/colibrInterface.py "+nameFile
			print exe2
			#val2=os.system(exe2)
			val2=0

			if val2==0:

				#os.chdir(script_dir + "/colibri_2073/")

				print "Translation for COLIBRI succeed!"
				exeCOLIBRI="./smt_colibri_local_linux.sh"

				print exeCOLIBRI
				exeCOLIBRI=shlex.split(exeCOLIBRI)

				#with open(resultFolder+"/COLIBRI.txt","w+") as colibri:
				#	c=subprocess.Popen(exeCOLIBRI,shell=False,preexec_fn=os.setsid,stdout=colibri,stderr=colibri)
				# processes.append(c)

				timer = Timer(timeout, mykill, [processes])

				try:
					timer.start()
					for process in processes:
						process.wait()
				finally:
					timer.cancel()
			else:
				print "Translation FAILURE!"
				exit(1)
		else:
				print "Translation FAILURE!"
				exit(1)
	else:
		print "Translation FAILURE!"
		exit(1)
else:
	print "Translation FAILURE!"
	exit(1)
