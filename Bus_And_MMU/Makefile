.PHONY: prereqs clean msg
.DEFAULT_GOAL := msg

CURR_DIR=$(shell realpath .)
OUT_DIR=$(CURR_DIR)/out
CACHE_DIR=$(OUT_DIR)/.cache
OUT_SRC_DIR=$(OUT_DIR)/sources

define check_for_binary
	@$(1) --help > /dev/null 2>&1 || (echo "Could not find $(1). Install $(1) first"; exit 1)
endef

msg:
	@echo "To build a file, run 'make NameOfFile'"
	@echo "To run the built file, run 'make run_NameOfFile'"
	@echo "To test with valgrind the built file, run 'make test_NameOfFile'"
	@echo "To profile a file, run 'make profile_NameOfFile'"
	@echo "To count line of a file, run 'make loc_NameOfFile'"

prereqs:
	$(call check_for_binary,z3)
	$(call check_for_binary,fstar.exe)
	$(call check_for_binary,krml)
	$(call check_for_binary,gcc)
	@test -n "$(FSTAR_HOME)" || (echo "Environment variable FSTAR_HOME not set"; exit 1)
	@test -n "$(KREMLIN_HOME)" || (echo "Environment variable KREMLIN_HOME not set"; exit 1)
	@mkdir -p $(CACHE_DIR)
	@mkdir -p $(OUT_DIR)
	@mkdir -p $(OUT_SRC_DIR)
	@echo "F*: $(FSTAR_HOME) $(shell which fstar.exe)"
	@echo "kremlin: $(KREMLIN_HOME) $(shell which krml)"
	@echo "gprof: $(shell which gprof)"
	@echo "valgrind: $(shell which valgrind)"

KREMLIN_INCLUDES= -I . 
KREMLIN_WARNINGS_AS_ERRORS=
KREMLIN_OPTIONS= -d reachability -dast
FOR_GCC= -ccopt -O0

FILE_NO_PREFIX=-no-prefix Core.Lio -no-prefix Core.LioStar -no-prefix Bus.Lattice -no-prefix Core.Lattice

EXTRA_FILES:=$(EXTRA_FILES)

%: prereqs %.fst
	fstar.exe --include $(KREMLIN_HOME)/kremlib --odir $(OUT_DIR) --cache_dir $(CACHE_DIR) --codegen Kremlin $*.fst $(EXTRA_FILES) --log_types
	krml  $(KREMLIN_OPTIONS) $(KREMLIN_WARNINGS_AS_ERRORS) -warn-error +9 $(KREMLIN_INCLUDES) -tmpdir $(OUT_SRC_DIR) $(FILE_NO_PREFIX)  -no-prefix $* $(OUT_DIR)/out.krml $(FOR_GCC) assumed.c -o $(OUT_DIR)/$*


#Bus.Example: prereqs Bus.Example.fst
#	fstar.exe --include $(KREMLIN_HOME)/kremlib --odir $(OUT_DIR) --cache_dir $(CACHE_DIR) --codegen Kremlin Bus.Example.fst $(EXTRA_FILES) --log_types
#	krml  $(KREMLIN_OPTIONS) $(KREMLIN_WARNINGS_AS_ERRORS) -warn-error +9 $(KREMLIN_INCLUDES) -tmpdir $(OUT_SRC_DIR) $(FILE_NO_PREFIX)  -no-prefix Bus.Example $(OUT_DIR)/out.krml $(FOR_GCC) assumed.c -o $(OUT_DIR)/Bus.Example


run_%:
	$(OUT_DIR)/$*

test_%:
	valgrind -v --leak-check=full $(OUT_DIR)/$*

profile_%: clean prereqs %.fst
	fstar.exe --include $(KREMLIN_HOME)/kremlib --odir $(OUT_DIR) --cache_dir $(CACHE_DIR) --codegen Kremlin $*.fst $(EXTRA_FILES) --log_types
	krml  $(KREMLIN_OPTIONS) $(KREMLIN_WARNINGS_AS_ERRORS) -warn-error +9 $(KREMLIN_INCLUDES) -tmpdir $(OUT_SRC_DIR) $(FILE_NO_PREFIX)  -no-prefix $* $(OUT_DIR)/out.krml $(FOR_GCC) -ccopt -pg assumed.c -o $(OUT_DIR)/$*
	make run_$*
	gprof $(OUT_DIR)/$* > Results.txt




loc_%: %.fst
	@echo "File have " `grep -cv -e '^\s*\$$' -e '^\s*//' -e '^\$$' -e '^\s*\[' -e '^\s*(\*' $^` "line(s)"

loc_gen: 
	@echo "Note: you must have generated source with LioStar and Lio without cleanning in between"
	@echo "      cloc must be installed to count lines"
	@echo ""
	@echo "Lio files ---------------------------------"
	cloc out/sources/Core_Lio.{c,h}
	@echo "LioStar files -----------------------------"
	cloc out/sources/Core_LioStar.{c,h}
	@echo "BusStar files -----------------------------"
	cloc out/sources/Bus_Lattice.{c,h}
	cloc out/sources/Bus_Example.{c,h}



clean:
	rm -rf $(OUT_DIR)
