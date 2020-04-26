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

prereqs:
	$(call check_for_binary,z3)
	$(call check_for_binary,fstar.exe)
	$(call check_for_binary,krml)
	@test -n "$(FSTAR_HOME)" || (echo "Environment variable FSTAR_HOME not set"; exit 1)
	@test -n "$(KREMLIN_HOME)" || (echo "Environment variable KREMLIN_HOME not set"; exit 1)
	@mkdir -p $(CACHE_DIR)
	@mkdir -p $(OUT_DIR)
	@mkdir -p $(OUT_SRC_DIR)
	@echo "F*: $(FSTAR_HOME) $(shell which fstar.exe)"
	@echo "kremlin: $(KREMLIN_HOME) $(shell which krml)"

KREMLIN_INCLUDES= -I . -I includes
#-add-include "\"assumed.c"\"
#-include . -add-include "\"IO.h\""
KREMLIN_WARNINGS_AS_ERRORS=
#-warn-error "@1..6@8..13"
KREMLIN_OPTIONS= -d reachability -warn-error +9 
# -skip-compilation
#-dast
FOR_GCC= -ccopt -O0 assumed.c

FILE_NO_PREFIX=-no-prefix Clients.Dummy -no-prefix LioStar.Effect -no-prefix LioStar.Box -no-prefix LatticeUsed

EXTRA_FILES:=$(EXTRA_FILES)

%: prereqs %.fst
	fstar.exe --include $(KREMLIN_HOME)/kremlib --odir $(OUT_DIR) --cache_dir $(CACHE_DIR) --codegen Kremlin $*.fst $(EXTRA_FILES) --log_types
	krml $(KREMLIN_OPTIONS) $(KREMLIN_WARNINGS_AS_ERRORS) $(KREMLIN_INCLUDES) -tmpdir $(OUT_SRC_DIR) $(FILE_NO_PREFIX) $(OUT_DIR)/out.krml $(FOR_GCC) -o $(OUT_DIR)/$*

run_%:
	$(OUT_DIR)/$*

test_%:
	valgrind -v --leak-check=full $(OUT_DIR)/$*

clean:
	rm -rf $(OUT_DIR)

profile_%: clean prereqs %.fst
	fstar.exe --include $(KREMLIN_HOME)/kremlib --odir $(OUT_DIR) --cache_dir $(CACHE_DIR) --codegen Kremlin $*.fst $(EXTRA_FILES) --log_types
	krml  $(KREMLIN_OPTIONS) $(KREMLIN_WARNINGS_AS_ERRORS) -warn-error +9 $(KREMLIN_INCLUDES) -tmpdir $(OUT_SRC_DIR) $(FILE_NO_PREFIX)  -no-prefix $* $(OUT_DIR)/out.krml $(FOR_GCC) -ccopt -pg -o $(OUT_DIR)/$*
	make run_$*
	gprof $(OUT_DIR)/$* > Results.txt

