include ../etc/sail.mk

.DELETE_ON_ERROR: cheri128.c cheri.c

MIPS_SAIL_DIR:=../mips
CHERI_SAIL_DIR:=.

TRACE?=no
ifeq ($(TRACE),yes)
TRACE_SAIL=trace.sail
else
TRACE_SAIL=notrace.sail
endif

MONO_REWRITES=$(SAIL_LIB_DIR)/mono_rewrites.sail

MIPS_PRE:=$(MIPS_SAIL_DIR)/$(TRACE_SAIL) $(MIPS_SAIL_DIR)/prelude.sail $(MIPS_SAIL_DIR)/mips_prelude.sail
MIPS_TLB:=$(MIPS_SAIL_DIR)/mips_tlb.sail
MIPS_TLB_STUB:=$(MIPS_SAIL_DIR)/mips_tlb_stub.sail
MIPS_INSTS:=$(MIPS_SAIL_DIR)/mips_insts.sail
MIPS_EPILOGUE:=$(MIPS_SAIL_DIR)/mips_ri.sail $(MIPS_SAIL_DIR)/mips_epilogue.sail
CHERI_PRE:=$(CHERI_SAIL_DIR)/cheri_types.sail $(CHERI_SAIL_DIR)/cheri_prelude_256.sail $(CHERI_SAIL_DIR)/cheri_prelude_common.sail  $(MIPS_SAIL_DIR)/mips_ast_decl.sail
CHERI128_PRE:=$(CHERI_SAIL_DIR)/cheri_types.sail $(CHERI_SAIL_DIR)/cheri_prelude_128.sail $(CHERI_SAIL_DIR)/cheri_prelude_common.sail $(MIPS_SAIL_DIR)/mips_ast_decl.sail
CHERI_INSTS:=$(CHERI_SAIL_DIR)/cheri_insts.sail

CHERI_SAILS:=$(MIPS_PRE) $(MIPS_TLB) $(CHERI_PRE) $(MIPS_INSTS) $(CHERI_INSTS) $(MIPS_EPILOGUE)
CHERI_SAILS_NOMIPS:=$(MIPS_PRE) $(MIPS_TLB) $(CHERI_PRE) $(CHERI_INSTS) $(MIPS_EPILOGUE)
CHERI_MONO_SAILS:=$(MIPS_PRE) $(SAIL_LIB_DIR)/mono_rewrites.sail $(MIPS_TLB) $(CHERI_PRE) $(MIPS_INSTS) $(CHERI_INSTS) $(MIPS_EPILOGUE)
CHERI_NO_TLB_SAILS:=$(MIPS_PRE) $(MIPS_TLB_STUB) $(CHERI_PRE) $(MIPS_INSTS) $(CHERI_INSTS) $(MIPS_EPILOGUE)
CHERI128_SAILS:=$(MIPS_PRE) $(MIPS_TLB) $(CHERI128_PRE) $(MIPS_INSTS) $(CHERI_INSTS) $(MIPS_EPILOGUE)
CHERI128_SAILS_NOMIPS:=$(MIPS_PRE) $(MIPS_TLB) $(CHERI128_PRE) $(CHERI_INSTS) $(MIPS_EPILOGUE)
CHERI128_NO_TLB_SAILS:=$(MIPS_PRE) $(MIPS_TLB_STUB) $(CHERI128_PRE) $(MIPS_INSTS) $(CHERI_INSTS) $(MIPS_EPILOGUE)
CHERI_MAIN:=$(MIPS_SAIL_DIR)/main.sail

cheri: $(CHERI_SAILS) $(CHERI_MAIN)
	$(SAIL) -ocaml_build_dir _sbuild_cheri -ocaml -o $@ $^

cheri_coverage: $(CHERI_SAILS) $(CHERI_MAIN)
	$(SAIL) -ocaml-coverage -ocaml -o $@ $^

cheri_trace: $(CHERI_SAILS) $(CHERI_MAIN)
	$(SAIL) -ocaml_trace -o $@ $^

coverage_report: bisect*.out
	bisect-ppx-report -I _sbuild/_build -html $@ $^

SAIL_OPT=-O -Oconstant_fold
cheri.c: $(CHERI_SAILS) $(CHERI_MAIN)
	$(SAIL) -memo_z3 $(SAIL_OPT) -c $^ 1> $@

C_OPT=-O3 -flto
GCOV_FLAGS=
cheri_c: cheri.c $(SAIL_LIB_DIR)/sail.h Makefile
	gcc $(C_OPT) $(GCOV_FLAGS) $< $(SAIL_LIB_DIR)/*.c -lgmp -lz -I $(SAIL_LIB_DIR) -o $@

# Note that for coverage purposes O1 appears optimal. O0 means lots of obviously dead code but O2 risks reducing granularity too much.
cheri_c_gcov: C_OPT=-O1
cheri_c_gcov: GCOV_FLAGS=-fprofile-arcs -ftest-coverage
cheri_c_gcov: cheri_c

gcovr:
	gcovr -r . --html --html-detail -o index.html

cheri128_smt: $(CHERI128_NO_TLB_SAILS) properties_128.sail
	$(SAIL) -smt -undefined_gen -memo_z3 $^

latex_128: $(CHERI128_SAILS_NOMIPS)
	rm -rf sail_latex_mips
	$(SAIL) -latex -latex_prefix sailMIPS -o sail_latex_mips $^

latex_256: $(CHERI_SAILS_NOMIPS)
	rm -rf sail_latex_mips_256
	$(SAIL) -latex -latex_prefix sailMIPS256 -o sail_latex_mips_256 $^

latex: latex_128 latex_256

cheri128: $(CHERI128_SAILS) $(CHERI_MAIN)
	$(SAIL) -ocaml_build_dir _sbuild_cheri128 -ocaml -o $@ $^

cheri128_trace: $(CHERI128_SAILS) $(CHERI_MAIN)
	$(SAIL) -ocaml_trace -o $@ $^

cheri128.c: $(CHERI128_SAILS) $(CHERI_MAIN)
	$(SAIL) -memo_z3 $(SAIL_OPT) -c $^ 1> $@

cheri128_c: cheri128.c $(SAIL_LIB_DIR)/sail.h Makefile
	gcc $(C_OPT) $(GCOV_FLAGS) $< $(SAIL_LIB_DIR)/*.c -lgmp -lz -I $(SAIL_LIB_DIR) -o $@


# test Ott raw pp
.PHONY: cheri128_ast
cheri128_ast: $(CHERI128_SAILS) $(CHERI_MAIN)
	../../sail/sail -ddump_tc_ast_ott_raw ../generated_definitions/ast/cheri128-ast-raw.txt -ddump_tc_ast_ott_pp ../generated_definitions/ast/cheri128-ast-pp.txt -ocaml -o $@ $^


# Note that for coverage purposes O1 appears optimal. O0 means lots of obviously dead code but O2 risks reducing granularity too much.
cheri128_c_gcov: C_OPT=-O1
cheri128_c_gcov: GCOV_FLAGS=-fprofile-arcs -ftest-coverage
cheri128_c_gcov: cheri128_c

LOC_FILES:=$(CHERI_SAILS) $(CHERI_MAIN)
include ../etc/loc.mk

# TODO Using bit lists for now in Lem generation; for machine words,
# monomorphisation is needed due to some variable length bitvectors, e.g. in
# CLoad as of commit b34c3fb, in the TLB translation, and in compressed
# capability functions

cheri_no_tlb.lem: $(MONO_REWRITES) $(CHERI_NO_TLB_SAILS)
	$(SAIL) -lem -o cheri_no_tlb -auto_mono -mono_rewrites -lem_mwords -lem_lib Mips_extras -undefined_gen -memo_z3 $^
cheri_no_tlb_types.lem: cheri_no_tlb.lem

cheri.lem: $(MONO_REWRITES) $(CHERI_SAILS) $(CHERI_MAIN)
	$(SAIL) -lem -o cheri -auto_mono -mono_rewrites -lem_mwords -lem_lib Mips_extras -undefined_gen -memo_z3 $^
cheri_types.lem: cheri.lem

cheri128_no_tlb.lem: $(MONO_REWRITES) $(CHERI128_NO_TLB_SAILS)
	$(SAIL) -lem -o cheri128_no_tlb -auto_mono -mono_rewrites -lem_mwords -lem_lib Mips_extras -undefined_gen -memo_z3 $^
cheri128_no_tlb_types.lem: cheri128_no_tlb.lem

cheri128.lem: $(MONO_REWRITES) $(CHERI128_SAILS)
	$(SAIL) -lem -o cheri128 -auto_mono -mono_rewrites -lem_mwords -lem_lib Mips_extras -undefined_gen -memo_z3 $^
cheri128_types.lem: cheri128.lem

C%.thy: c%.lem c%_types.lem $(MIPS_SAIL_DIR)/mips_extras.lem
	lem -isa -outdir . -lib Sail=$(SAIL_DIR)/src/gen_lib -lib Sail=$(SAIL_DIR)/src/lem_interp $^
	sed -i 's/datatype ast/datatype (plugins only: size) ast/' C$*_types.thy

%Script.sml: %.lem %_types.lem $(MIPS_SAIL_DIR)/mips_extras.lem
	lem -hol -outdir . -lib $(SAIL_DIR)/lib/hol -i $(SAIL_DIR)/lib/hol/sail2_prompt_monad.lem -i $(SAIL_DIR)/lib/hol/sail2_prompt.lem -lib $(SAIL_DIR)/src/gen_lib -lib $(SAIL_DIR)/src/lem_interp $^

%Theory.uo: %Script.sml
	SAIL_LIB_DIR="$(SAIL_LIB_DIR)" Holmake $@

cheri.v cheri_types.v: $(CHERI_SAILS) $(CHERI_SAIL_DIR)/cheri_termination.sail
	$(SAIL) -coq -o cheri -coq_lib mips_extras -undefined_gen -memo_z3 -dcoq_undef_axioms $^

cheri128.v cheri128_types.v: $(CHERI128_SAILS) $(CHERI_SAIL_DIR)/cheri_termination.sail
	$(SAIL) -coq -o cheri128 -coq_lib mips_extras -undefined_gen -memo_z3 -dcoq_undef_axioms $^

CHERI_COQ = cheri_types.v mips_extras.v cheri.v
CHERI128_COQ = cheri128_types.v mips_extras.v cheri128.v
#COQ_LIBS = -Q $(SAIL_DIR)/../bbv/theories bbv -Q $(SAIL_DIR)/lib/coq Sail -R ../mips ''
COQ_LIBS = -R ../mips ''

%.vo: %.v
	coqc $(COQ_LIBS) $<
cheri.vo: cheri_types.vo ../mips/mips_extras.vo
cheri128.vo: cheri128_types.vo ../mips/mips_extras.vo

CHERI_CC_QTEST_BUILD=cheri_cc_qtest_build

$(CHERI_CC_QTEST_BUILD): ../mips/prelude.sail ../mips/notrace.sail ../mips/mips_prelude.sail ../mips/mips_tlb_stub.sail ../mips/mips_wrappers.sail cheri_types.sail cheri_prelude_128.sail
	$(SAIL) -ocaml -ocaml-nobuild -ocaml_build_dir $@ -o cheri_cc $^

cheri_cc_qtest: $(CHERI_CC_QTEST_BUILD)
	cp cheri_cc_qtest.ml $(CHERI_CC_QTEST_BUILD)/main.ml
	cd $(CHERI_CC_QTEST_BUILD) && \
	ocamlbuild -use-ocamlfind -tag 'package(qcheck)' main.native

qtest: cheri_cc_qtest
	./cheri_cc_qtest_build/main.native --verbose

clean:
	rm -rf cheri cheri_trace cheri_coverage cheri_c cheri128 cheri128_trace cheri128_c _sbuild _sbuild_cheri _sbuild_cheri128 inst_*.sail cheri.c cheri128.c sail_latex sail_latexcc sail_latex_mips sail_latex_mips_256 coverage_report
	rm -f cheriScript.sml cheri_typesScript.sml mips_extrasScript.sml
	rm -f cheri.v cheri_types.v $(CHERI_COQ:%.v=%.vo) $(CHERI_COQ:%.v=%.glob) $(CHERI_COQ:%.v=.%.aux)
	rm -f cheri128.v cheri128_types.v $(CHERI128_COQ:%.v=%.vo) $(CHERI128_COQ:%.v=%.glob) $(CHERI128_COQ:%.v=.%.aux)
	-Holmake cleanAll
