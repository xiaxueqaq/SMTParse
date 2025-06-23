.PHONY: clean
all:make_python_lib smt2_to_mma random_NRA
## Load Previous Configuration ####################################################################

-include config.mk

## Configurable options ###########################################################################

# Directory to store object files, libraries, executables, and dependencies:
smtlib_parse_BUILD_DIR      ?= build
smtlib_parse_LIB_DIR   ?=lib
# Include debug-symbols in release builds
smtlib_parse_RELSYM ?= -g

# Sets of compile flags for different build types
smtlib_parse_REL    ?= -O3 
smtlib_parse_DEB    ?=  -g -D DEBUG 
smtlib_parse_PRF    ?= -O3 -D NDEBUG
smtlib_parse_FPIC   ?= -fpic

# GNU Standard Install Prefix
smtlib_parse_prefix         ?= /usr/local

config:
	@( echo 'smtlib_parse_BUILD_DIR?=$(smtlib_parse_BUILD_DIR)'           ; \
	   echo 'smtlib_parse_LIB_DIR?=$(smtlib_parse_LIB_DIR)'           ; \
	   echo 'smtlib_parse_RELSYM?=$(smtlib_parse_RELSYM)' ; \
	   echo 'smtlib_parse_REL?=$(smtlib_parse_REL)'       ; \
	   echo 'smtlib_parse_DEB?=$(smtlib_parse_DEB)'       ; \
	   echo 'smtlib_parse_PRF?=$(smtlib_parse_PRF)'       ; \
	   echo 'smtlib_parse_FPIC?=$(smtlib_parse_FPIC)'     ; \
	   echo 'smtlib_parse_prefix?=$(smtlib_parse_prefix)'                 ) > config.mk

smtlib_parse_hh=$(wildcard src/*.hh)
CXX=g++ 
IPATHS=-ICLPoly/ -I./src
Ipython=-I/usr/include/python3.10
CFLAGS=-O3 -flto 

clpolylib= -LCLPoly/lib/clpoly  -lclpoly -lgmpxx -lgmp
pythonlib=-lboost_python3  
smtlib_parse_hh=$(wildcard src/*.hh)
smtlib_parse_cc_=$(wildcard src/*.cc)
main_cc=src/smt2_to_mma.cc src/random_NRA.cc src/chordofsmt.cc
smtlib_parse_cc=$(filter-out $(main_cc),$(smtlib_parse_cc_))
smtlib_parse_d_o=$(smtlib_parse_cc:src/%.cc=$(smtlib_parse_BUILD_DIR)/debug/smtlib_parse/%.o)
smtlib_parse_r_o=$(smtlib_parse_cc:src/%.cc=$(smtlib_parse_BUILD_DIR)/release/smtlib_parse/%.o)
$(smtlib_parse_BUILD_DIR)/release/smtlib_parse/%.o:src/%.cc $(smtlib_parse_hh)
	mkdir -p $(smtlib_parse_BUILD_DIR)/release/smtlib_parse
	$(CXX) $(smtlib_parse_REL) $(smtlib_parse_FPIC) $(IPATHS) -c $< -o $@ $(clpolylib)
$(smtlib_parse_BUILD_DIR)/debug/%.o:%.cc $(smtlib_parse_hh)
	mkdir -p $(smtlib_parse_BUILD_DIR)/debug/smtlib_parse
	$(CXX) $(smtlib_parse_DEB) $(smtlib_parse_FPIC) $(IPATHS) -c $< -o $@ $(clpolylib)

$(smtlib_parse_LIB_DIR)/smtlib_parse/NRA_op.so:$(smtlib_parse_r_o) python/NRA_op.cc
	mkdir -p $(dir $@)
	$(CXX) $(smtlib_parse_REL) $(smtlib_parse_FPIC) $(IPATHS) $(Ipython) $(smtlib_parse_r_o) python/NRA_op.cc -shared -o  $@ $(clpolylib) $(pythonlib)
make_python_lib:$(smtlib_parse_LIB_DIR)/smtlib_parse/NRA_op.so
smt2_to_mma:$(smtlib_parse_r_o)  src/smt2_to_mma.cc
	$(CXX) $(smtlib_parse_REL) $(smtlib_parse_FPIC) $(IPATHS) $(smtlib_parse_r_o) src/$@.cc -o  $@  $(clpolylib)
chordofsmt:$(smtlib_parse_r_o)  src/chordofsmt.cc
	$(CXX) $(smtlib_parse_REL) $(smtlib_parse_FPIC) $(IPATHS) $(smtlib_parse_r_o) src/$@.cc -o  $@  $(clpolylib)

random_NRA:$(smtlib_parse_r_o)  src/random_NRA.cc
	$(CXX) $(smtlib_parse_REL) $(smtlib_parse_FPIC) $(IPATHS) $(smtlib_parse_r_o) src/$@.cc -o  $@  $(clpolylib) 

clean:
	rm -r $(smtlib_parse_d_o) $(smtlib_parse_r_o) $(smtlib_parse_LIB_DIR)/smtlib_parse/NRA_op.so random_NRA smt2_to_mma