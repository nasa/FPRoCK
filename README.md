FPRoCK
------

*FPRoCK v-0.1* (February 2019)

*FPRoCK* (Floating-Point and Real ChecKer) is a prototype tool that decides the satisfiability of a mixed real and floating-point formula.
To this aim, it transforms a mixed formula into an equi-satisfiable one over the reals.
This transformed formula is then input to different off-the-shelf SMT solvers for resolution.
FPRoCK returns an assignment satisfying the formula if it exists; otherwise, it returns `unsat` indicating that the set is unsatisfiable.

The input to *FPRoCK* is a text file containing the following information:

* the list of floating-point variables with their precision (single or double) and *optional* initial range, for example:

```
Float: X[double] = [-2000.0;2000.0],
       Y[double] = [-2000.0;2000.0]
```

* the list of real variables with their *optional* initial range, for example:

```
Real: Real_X[real] = [-2000.0;2000.0],
      Real_Y[real] = [-2000.0;2000.0],
      Err_X[real],
      Err_Y[real]
```

* the set of constraints/formulas to check for satisfiability, for example:

```
Err_X >= abs(Real_X - X)
Err_Y >= abs(Real_Y - Y)
Err_X = 1.1368683772161603e-13
Err_Y = 1.1368683772161603e-13
```

In its current version, *FPRoCK* supports conjuntions (and), negations (not), equalities and disequalities (=, !=, <, >, <=, >=)  basic arithmetic operators over the reals (+,-,\*,/) and over the floats (+FP,-FP,\*FP,/FP), and the absolute value operator (abs).
Constant integer values are required to be written with a .0 at the end, e.g. 2.0. Scientific format is also accepted, e.g. 1.1368683772161603e-13.

Prerequisites
-------------

To install *FPRoCK* you will need to install:

* Python 2.7 and pip
    * install the `bigfloat` library with the command `pip install bigfloat`
* MathSAT (http://mathsat.fbk.eu/)
* Z3 (https://github.com/Z3Prover/z3)
* CVC4 (http://cvc4.cs.stanford.edu/web/)
* Colibri (https://soprano-project.fr/download_colibri.html)

The SMT solvers and the python interpreter should be available in the `PATH` environment variable.


Installation and use
--------------------

To install *FPRoCK* the repository has to be copied to a desired location. For example, with `git` we can clone the repository in the `/fprock` folder:

```
git clone https://github.com/nasa/FPRoCK.git /fprock
```

To execute *FPRoCK* the `executor.py` script has to be called from the root folder of the repository:

```
cd /fprock
python executor.py
```

The last command will display some usage help.

For example, to check the benchmark `eps-line/ceb_5.fpr` (which is `unsat`) you have to specify a timeout, a rounding mode and an input file in sequence, as in:

```
python executor.py 10 rnd-to-zero  benchmarks/eps_line/ceb_5.fpr
```

*FPRoCK* will create a directory `results` with one file of results for each combination of SMT solver and search strategy used.
The result of *FPRoCK* is the content of those files.
For example, to check the result of the previous example you can execute a command like:

```
cat results/*
```

And you would get an output like the following telling you that the formula is `unsat`:

```
unsat
(error "Cannot get the current model unless immediately preceded by SAT/INVALID or UNKNOWN response.")
unsat
(error "model generation not enabled")
unsat
(error "model generation not enabled")
unsat
(error "model generation not enabled")
unsat
(error "line 13029 column 10: model is not available")
unsat
(error "line 4344 column 10: model is not available")
unsat
(error "line 6580 column 10: model is not available")
```

Some result files maybe empty because the SMT timed out. The different results should all agree. If two different results `sat`/`unsat` are found for a problem it should be reported since it would imply an error in *FPRoCK* or in the underlying SMT solvers used.


Using Docker
------------

A `Dockerfile` is provided in the `/fprock/Docker/` folder in order to build a *Docker* image that can be use to install and run automatically *FPRoCK*.
The [Docker](https://www.docker.com/) tool has to be installed in order to use this approach.
The following commands build and run a *Docker* image with *FPRoCK*:

```
cd /fprock/Docker
docker build -t fprock .
docker run -it fprock /bin/bash
```

When running an *FPRoCK* image the tool is executed identically:

```
cd  /fprock
python executor.py 10 rnd-to-zero  benchmarks/eps_line/ceb_5.fpr
```


Contact information
-------------------

[C&eacute;sar A. Mu&ntilde;oz](http://shemesh.larc.nasa.gov/people/cam)

### License and Copyright Notice

The code in this repository is released under NASA's Open Source
Agreement.  See the directory [`LICENSES`](LICENSES).

<pre>

Notices:

Copyright 2019 United States Government as represented by the
   Administrator of the National Aeronautics and Space Administration.
   All Rights Reserved.

Disclaimers:

No Warranty: THE SUBJECT SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY
WARRANTY OF ANY KIND, EITHER EXPRESSED, IMPLIED, OR STATUTORY,
INCLUDING, BUT NOT LIMITED TO, ANY WARRANTY THAT THE SUBJECT SOFTWARE
WILL CONFORM TO SPECIFICATIONS, ANY IMPLIED WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE, OR FREEDOM FROM
INFRINGEMENT, ANY WARRANTY THAT THE SUBJECT SOFTWARE WILL BE ERROR
FREE, OR ANY WARRANTY THAT DOCUMENTATION, IF PROVIDED, WILL CONFORM TO
THE SUBJECT SOFTWARE.  THIS AGREEMENT DOES NOT, IN ANY MANNER,
CONSTITUTE AN ENDORSEMENT BY GOVERNMENT AGENCY OR ANY PRIOR RECIPIENT
OF ANY RESULTS, RESULTING DESIGNS, HARDWARE, SOFTWARE PRODUCTS OR ANY
OTHER APPLICATIONS RESULTING FROM USE OF THE SUBJECT SOFTWARE.
FURTHER, GOVERNMENT AGENCY DISCLAIMS ALL WARRANTIES AND LIABILITIES
REGARDING THIRD-PARTY SOFTWARE, IF PRESENT IN THE ORIGINAL SOFTWARE,
AND DISTRIBUTES IT "AS IS."

Waiver and Indemnity: RECIPIENT AGREES TO WAIVE ANY AND ALL CLAIMS
AGAINST THE UNITED STATES GOVERNMENT, ITS CONTRACTORS AND
SUBCONTRACTORS, AS WELL AS ANY PRIOR RECIPIENT.  IF RECIPIENT'S USE OF
THE SUBJECT SOFTWARE RESULTS IN ANY LIABILITIES, DEMANDS, DAMAGES,
EXPENSES OR LOSSES ARISING FROM SUCH USE, INCLUDING ANY DAMAGES FROM
PRODUCTS BASED ON, OR RESULTING FROM, RECIPIENT'S USE OF THE SUBJECT
SOFTWARE, RECIPIENT SHALL INDEMNIFY AND HOLD HARMLESS THE UNITED
STATES GOVERNMENT, ITS CONTRACTORS AND SUBCONTRACTORS, AS WELL AS ANY
PRIOR RECIPIENT, TO THE EXTENT PERMITTED BY LAW.  RECIPIENT'S SOLE
REMEDY FOR ANY SUCH MATTER SHALL BE THE IMMEDIATE, UNILATERAL
TERMINATION OF THIS AGREEMENT.

</pre>

