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

FROM ubuntu:18.04
LABEL maintainer.name="Marco A. Feliu" maintainer.email="marco.feliu@nianet.org"

ENV DEBIAN_FRONTEND=noninteractive

############################################################
# APT and PIP dependencies
############################################################

RUN apt-get update
RUN apt-get upgrade -yq
RUN apt-get install -yq git
RUN apt-get install -yq python2.7 python-pip
RUN apt-get install -yq libmpfr-dev
RUN pip install bigfloat

ARG FPROCK_HOME="/fprock"
ARG FPROCK_REPOSITORY=https://github.com/nasa/FPRoCK.git
ARG CVC4_URL=http://cvc4.cs.stanford.edu/downloads/builds/x86_64-linux-opt/cvc4-1.6-x86_64-linux-opt
ARG MATHSAT_URL=http://mathsat.fbk.eu/release/mathsat-5.5.3-linux-x86_64.tar.gz
ARG Z3_URL=https://github.com/Z3Prover/z3/archive/z3-4.8.3.tar.gz


############################################################
# FPRock
############################################################

RUN git clone ${FPROCK_REPOSITORY} ${FPROCK_HOME}}


############################################################
# SMT solvers
############################################################

RUN mkdir -p ${FPROCK_HOME}
WORKDIR ${FPROCK_HOME}
ADD ${CVC4_URL}    .
ADD ${MATHSAT_URL} .
ADD ${Z3_URL}      .

RUN mv cvc4-1.6-x86_64-linux-opt /usr/bin/cvc4
RUN chmod +x /usr/bin/cvc4

RUN tar xfz mathsat-5.5.3-linux-x86_64.tar.gz
RUN mv ./mathsat-5.5.3-linux-x86_64/bin/mathsat /usr/bin/mathsat
RUN chmod +x /usr/bin/mathsat

RUN tar xfz z3-4.8.3.tar.gz
WORKDIR ${FPROCK_HOME}/z3-z3-4.8.3
RUN python scripts/mk_make.py --python
RUN cd build;make -j9
RUN cd build;make install

WORKDIR ${FPROCK_HOME}
