CC = ocamlc
CFLAGS = -c

YACC = ocamlyacc
LEX = ocamllex

RM = rm
TOUCH = touch

EXEC_SUFFIX = cmo
EXP_SUFFIX = cmi


built_done: lie_type.$(EXEC_SUFFIX) lie_equiv.$(EXEC_SUFFIX) lie_match.$(EXEC_SUFFIX) lie_resolv.$(EXEC_SUFFIX) compiler_done lie_main.$(EXEC_SUFFIX)
	$(TOUCH) $@
compiler_done: lie_type.$(EXEC_SUFFIX) lie_parser.$(EXP_SUFFIX) lie_parser.$(EXEC_SUFFIX) lie_lexer.$(EXEC_SUFFIX)
	$(TOUCH) $@


lie_type.$(EXEC_SUFFIX): lie_type.ml
	$(CC) $(CFLAGS) $<
lie_equiv.$(EXEC_SUFFIX): lie_equiv.ml
	$(CC) $(CFLAGS) $<
lie_match.$(EXEC_SUFFIX): lie_match.ml
	$(CC) $(CFLAGS) $<
lie_resolv.$(EXEC_SUFFIX): lie_resolv.ml
	$(CC) $(CFLAGS) $<
lie_main.$(EXEC_SUFFIX): lie_main.ml
	$(CC) $(CFLAGS) $<

lie_parser.$(EXEC_SUFFIX): lie_parser.ml
	$(CC) $(CFLAGS) $<
lie_parser.$(EXP_SUFFIX): lie_parser.mli
	$(CC) $(CFLAGS) $<
lie_parser.ml: lie_parser.mly
	$(YACC) $<
lie_parser.mli: lie_parser.mly
	$(YACC) $<

lie_lexer.$(EXEC_SUFFIX): lie_lexer.ml
	$(CC) $(CFLAGS) $<
lie_lexer.ml: lie_lexer.mll
	$(LEX) $<


.PHONY: clean
clean:
	-$(RM) a.out
	-$(RM) compiler_done built_done
	-$(RM) lie_lexer.ml lie_parser.ml lie_parser.mli
	-$(RM) *.cmi
	-$(RM) *.cmo
	-$(RM) *~
