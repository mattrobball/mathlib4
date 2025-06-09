// Lean compiler output
// Module: Mathlib.Tactic.RunCmd
// Imports: Init Lean.Elab.Eval Std.Util.TermUnsafe
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
static lean_object* l_Mathlib_RunCmd_elabRunElab___closed__8;
static lean_object* l_Mathlib_RunCmd_runCmd___closed__1;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__7;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1477_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Mathlib_RunCmd_byElab___closed__6;
static lean_object* l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1477____closed__1;
static lean_object* l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__4;
static lean_object* l_Mathlib_RunCmd_runTac___closed__5;
static lean_object* l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1477____closed__2;
static lean_object* l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__6;
static lean_object* l_Mathlib_RunCmd_elabRunElab___closed__1;
lean_object* l_Lean_Elab_Command_getMainModule___rarg(lean_object*, lean_object*);
static lean_object* l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__2;
LEAN_EXPORT lean_object* l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_462_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__5;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__2;
static lean_object* l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__10;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Mathlib_RunCmd_byElab___closed__3;
static lean_object* l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__14;
static lean_object* l_Mathlib_RunCmd_byElab___closed__5;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
static lean_object* l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__12;
static lean_object* l_Mathlib_RunCmd_elabRunElab___closed__11;
static lean_object* l_Mathlib_RunCmd_runCmd___closed__2;
static lean_object* l_Mathlib_RunCmd_elabRunElab___closed__4;
static lean_object* l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_462____closed__3;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1___spec__1___rarg___closed__1;
static lean_object* l_Mathlib_RunCmd_elabRunElab___closed__2;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__13;
static lean_object* l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__3;
static lean_object* l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__11;
static lean_object* l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__14;
static lean_object* l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__6;
LEAN_EXPORT lean_object* l_Mathlib_RunCmd_runCmd;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1___spec__1___rarg___closed__2;
static lean_object* l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__15;
static lean_object* l_Mathlib_RunCmd_elabRunElab___closed__3;
static lean_object* l_Mathlib_RunCmd_runCmd___closed__5;
static lean_object* l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__2;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabAuxDef___spec__1___rarg(lean_object*);
static lean_object* l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__5;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(lean_object*);
static lean_object* l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__1;
LEAN_EXPORT lean_object* l_Array_sequenceMap_loop___at_Mathlib_RunCmd_elabRunElab___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__11;
static lean_object* l_Mathlib_RunCmd_runCmd___closed__9;
lean_object* l_Lean_Elab_Command_getRef(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_sequenceMap___at_Mathlib_RunCmd_elabRunElab___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Mathlib_RunCmd_runCmd___closed__4;
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__1;
static lean_object* l_Mathlib_RunCmd_runCmd___closed__11;
static lean_object* l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__3;
static lean_object* l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__6;
static lean_object* l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_462____closed__5;
static lean_object* l_Mathlib_RunCmd_elabRunElab___closed__7;
static lean_object* l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__7;
static lean_object* l_Mathlib_RunCmd_byElab___closed__2;
LEAN_EXPORT lean_object* l_Array_sequenceMap___at_Mathlib_RunCmd_elabRunElab___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope(lean_object*, lean_object*, lean_object*);
static lean_object* l_Mathlib_RunCmd_elabRunElab___closed__9;
static lean_object* l_Mathlib_RunCmd_runTac___closed__1;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__5;
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Mathlib_RunCmd_runTac___closed__3;
static lean_object* l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__9;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Mathlib_RunCmd_byElab;
static lean_object* l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__12;
static lean_object* l_Mathlib_RunCmd_runCmd___closed__3;
static lean_object* l_Mathlib_RunCmd_runCmd___closed__10;
static lean_object* l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__4;
LEAN_EXPORT lean_object* l_Mathlib_RunCmd_elabRunElab___lambda__2(lean_object*);
static lean_object* l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__3;
static lean_object* l_Mathlib_RunCmd_elabRunElab___closed__10;
static lean_object* l_Mathlib_RunCmd_byElab___closed__4;
static lean_object* l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__10;
static lean_object* l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__10;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_sequenceMap_loop___at_Mathlib_RunCmd_elabRunElab___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Mathlib_RunCmd_elabRunElab___closed__5;
static lean_object* l_Mathlib_RunCmd_byElab___closed__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
static lean_object* l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__9;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__13;
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Mathlib_RunCmd_elabRunElab___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Mathlib_RunCmd_elabRunElab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Mathlib_RunCmd_elabRunElab___closed__6;
static lean_object* l_Mathlib_RunCmd_runTac___closed__6;
static lean_object* l_Mathlib_RunCmd_runCmd___closed__7;
static lean_object* l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1___spec__1___rarg(lean_object*);
static lean_object* l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_462____closed__1;
static lean_object* l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__7;
lean_object* l_Lean_Elab_Term_evalTerm___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Mathlib_RunCmd_runCmd___closed__6;
static lean_object* l_Mathlib_RunCmd_runCmd___closed__8;
LEAN_EXPORT lean_object* l_Mathlib_RunCmd_runTac;
LEAN_EXPORT lean_object* l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Mathlib_RunCmd_runCmd___closed__12;
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
static lean_object* l_Mathlib_RunCmd_runCmd___closed__13;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__9;
lean_object* l_String_toSubstring_x27(lean_object*);
static lean_object* l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__4;
static lean_object* l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__8;
static lean_object* l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_462____closed__4;
static lean_object* l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_462____closed__2;
LEAN_EXPORT lean_object* l_Mathlib_RunCmd_elabRunElab___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Mathlib_RunCmd_runTac___closed__2;
static lean_object* l_Mathlib_RunCmd_runTac___closed__4;
static lean_object* _init_l_Mathlib_RunCmd_runCmd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Mathlib", 7);
return x_1;
}
}
static lean_object* _init_l_Mathlib_RunCmd_runCmd___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("RunCmd", 6);
return x_1;
}
}
static lean_object* _init_l_Mathlib_RunCmd_runCmd___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("runCmd", 6);
return x_1;
}
}
static lean_object* _init_l_Mathlib_RunCmd_runCmd___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Mathlib_RunCmd_runCmd___closed__1;
x_2 = l_Mathlib_RunCmd_runCmd___closed__2;
x_3 = l_Mathlib_RunCmd_runCmd___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Mathlib_RunCmd_runCmd___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("andthen", 7);
return x_1;
}
}
static lean_object* _init_l_Mathlib_RunCmd_runCmd___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Mathlib_RunCmd_runCmd___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Mathlib_RunCmd_runCmd___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("run_cmd ", 8);
return x_1;
}
}
static lean_object* _init_l_Mathlib_RunCmd_runCmd___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Mathlib_RunCmd_runCmd___closed__7;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Mathlib_RunCmd_runCmd___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("doSeq", 5);
return x_1;
}
}
static lean_object* _init_l_Mathlib_RunCmd_runCmd___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Mathlib_RunCmd_runCmd___closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Mathlib_RunCmd_runCmd___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Mathlib_RunCmd_runCmd___closed__10;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Mathlib_RunCmd_runCmd___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Mathlib_RunCmd_runCmd___closed__6;
x_2 = l_Mathlib_RunCmd_runCmd___closed__8;
x_3 = l_Mathlib_RunCmd_runCmd___closed__11;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Mathlib_RunCmd_runCmd___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Mathlib_RunCmd_runCmd___closed__4;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Mathlib_RunCmd_runCmd___closed__12;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Mathlib_RunCmd_runCmd() {
_start:
{
lean_object* x_1; 
x_1 = l_Mathlib_RunCmd_runCmd___closed__13;
return x_1;
}
}
static lean_object* _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Elab", 4);
return x_1;
}
}
static lean_object* _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Command", 7);
return x_1;
}
}
static lean_object* _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("CommandElabM", 12);
return x_1;
}
}
static lean_object* _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__1;
x_2 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__2;
x_3 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__3;
x_4 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__5;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Unit", 4);
return x_1;
}
}
static lean_object* _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__8;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__6;
x_2 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__9;
x_3 = l_Lean_Expr_app___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__10;
x_10 = 1;
x_11 = l_Lean_Elab_Term_evalTerm___rarg(x_9, x_1, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
static lean_object* _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Parser", 6);
return x_1;
}
}
static lean_object* _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Term", 4);
return x_1;
}
}
static lean_object* _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("app", 3);
return x_1;
}
}
static lean_object* _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__1;
x_2 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__1;
x_3 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__2;
x_4 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("discard", 7);
return x_1;
}
}
static lean_object* _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__5;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Functor", 7);
return x_1;
}
}
static lean_object* _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__8;
x_2 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__5;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("null", 4);
return x_1;
}
}
static lean_object* _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__12;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("do", 2);
return x_1;
}
}
static lean_object* _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__1;
x_2 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__1;
x_3 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__2;
x_4 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__14;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Mathlib_RunCmd_runCmd___closed__4;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabAuxDef___spec__1___rarg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
x_10 = l_Lean_Elab_Command_getRef(x_2, x_3, x_4);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = 0;
x_14 = l_Lean_SourceInfo_fromRef(x_11, x_13);
x_15 = l_Lean_Elab_Command_getCurrMacroScope(x_2, x_3, x_12);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Elab_Command_getMainModule___rarg(x_3, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__7;
x_22 = l_Lean_addMacroScope(x_19, x_21, x_16);
x_23 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__6;
x_24 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__11;
lean_inc(x_14);
x_25 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_25, 0, x_14);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_22);
lean_ctor_set(x_25, 3, x_24);
x_26 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__14;
lean_inc(x_14);
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_14);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__15;
lean_inc(x_14);
x_29 = l_Lean_Syntax_node2(x_14, x_28, x_27, x_9);
x_30 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__13;
lean_inc(x_14);
x_31 = l_Lean_Syntax_node1(x_14, x_30, x_29);
x_32 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__4;
x_33 = l_Lean_Syntax_node2(x_14, x_32, x_25, x_31);
x_34 = lean_alloc_closure((void*)(l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203_), 8, 1);
lean_closure_set(x_34, 0, x_33);
x_35 = l_Lean_Elab_Command_liftTermElabM___rarg(x_34, x_2, x_3, x_20);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_apply_3(x_36, x_2, x_3, x_37);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_3);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_35);
if (x_39 == 0)
{
return x_35;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_35, 0);
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_35);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
static lean_object* _init_l_Mathlib_RunCmd_runTac___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("runTac", 6);
return x_1;
}
}
static lean_object* _init_l_Mathlib_RunCmd_runTac___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Mathlib_RunCmd_runCmd___closed__1;
x_2 = l_Mathlib_RunCmd_runCmd___closed__2;
x_3 = l_Mathlib_RunCmd_runTac___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Mathlib_RunCmd_runTac___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("run_tac ", 8);
return x_1;
}
}
static lean_object* _init_l_Mathlib_RunCmd_runTac___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Mathlib_RunCmd_runTac___closed__3;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Mathlib_RunCmd_runTac___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Mathlib_RunCmd_runCmd___closed__6;
x_2 = l_Mathlib_RunCmd_runTac___closed__4;
x_3 = l_Mathlib_RunCmd_runCmd___closed__11;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Mathlib_RunCmd_runTac___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Mathlib_RunCmd_runTac___closed__2;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Mathlib_RunCmd_runTac___closed__5;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Mathlib_RunCmd_runTac() {
_start:
{
lean_object* x_1; 
x_1 = l_Mathlib_RunCmd_runTac___closed__6;
return x_1;
}
}
static lean_object* _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_462____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Tactic", 6);
return x_1;
}
}
static lean_object* _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_462____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("TacticM", 7);
return x_1;
}
}
static lean_object* _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_462____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__1;
x_2 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__2;
x_3 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_462____closed__1;
x_4 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_462____closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_462____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_462____closed__3;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_462____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_462____closed__4;
x_2 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__9;
x_3 = l_Lean_Expr_app___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_462_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_462____closed__5;
x_10 = 1;
x_11 = l_Lean_Elab_Term_evalTerm___rarg(x_9, x_1, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_unsupportedSyntaxExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1___spec__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1___spec__1___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1___spec__1___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1___spec__1___rarg), 1, 0);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Mathlib_RunCmd_runTac___closed__2;
lean_inc(x_1);
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1___spec__1___rarg(x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
x_16 = lean_ctor_get(x_8, 5);
lean_inc(x_16);
x_17 = 0;
x_18 = l_Lean_SourceInfo_fromRef(x_16, x_17);
x_19 = lean_ctor_get(x_8, 10);
lean_inc(x_19);
x_20 = lean_st_ref_get(x_9, x_10);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_environment_main_module(x_23);
x_25 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__7;
x_26 = l_Lean_addMacroScope(x_24, x_25, x_19);
x_27 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__6;
x_28 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__11;
lean_inc(x_18);
x_29 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_29, 0, x_18);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_26);
lean_ctor_set(x_29, 3, x_28);
x_30 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__14;
lean_inc(x_18);
x_31 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_31, 0, x_18);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__15;
lean_inc(x_18);
x_33 = l_Lean_Syntax_node2(x_18, x_32, x_31, x_15);
x_34 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__13;
lean_inc(x_18);
x_35 = l_Lean_Syntax_node1(x_18, x_34, x_33);
x_36 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__4;
x_37 = l_Lean_Syntax_node2(x_18, x_36, x_29, x_35);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_38 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_462_(x_37, x_4, x_5, x_6, x_7, x_8, x_9, x_22);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_apply_9(x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_40);
return x_41;
}
else
{
uint8_t x_42; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
return x_38;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_38, 0);
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_38);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_throwUnsupportedSyntax___at_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l_Mathlib_RunCmd_byElab___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("byElab", 6);
return x_1;
}
}
static lean_object* _init_l_Mathlib_RunCmd_byElab___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Mathlib_RunCmd_runCmd___closed__1;
x_2 = l_Mathlib_RunCmd_runCmd___closed__2;
x_3 = l_Mathlib_RunCmd_byElab___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Mathlib_RunCmd_byElab___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("by_elab ", 8);
return x_1;
}
}
static lean_object* _init_l_Mathlib_RunCmd_byElab___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Mathlib_RunCmd_byElab___closed__3;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Mathlib_RunCmd_byElab___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Mathlib_RunCmd_runCmd___closed__6;
x_2 = l_Mathlib_RunCmd_byElab___closed__4;
x_3 = l_Mathlib_RunCmd_runCmd___closed__11;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Mathlib_RunCmd_byElab___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Mathlib_RunCmd_byElab___closed__2;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Mathlib_RunCmd_byElab___closed__5;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Mathlib_RunCmd_byElab() {
_start:
{
lean_object* x_1; 
x_1 = l_Mathlib_RunCmd_byElab___closed__6;
return x_1;
}
}
static lean_object* _init_l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("x", 1);
return x_1;
}
}
static lean_object* _init_l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Option", 6);
return x_1;
}
}
static lean_object* _init_l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__4;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Expr", 4);
return x_1;
}
}
static lean_object* _init_l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__1;
x_2 = l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__6;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__7;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__5;
x_2 = l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__8;
x_3 = l_Lean_Expr_app___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("TermElabM", 9);
return x_1;
}
}
static lean_object* _init_l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__1;
x_2 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__2;
x_3 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__2;
x_4 = l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__10;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__11;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__12;
x_2 = l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__8;
x_3 = l_Lean_Expr_app___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__2;
x_2 = l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__9;
x_3 = l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__13;
x_4 = 0;
x_5 = l_Lean_Expr_forallE___override(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__14;
x_10 = 1;
x_11 = l_Lean_Elab_Term_evalTerm___rarg(x_9, x_1, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
static lean_object* _init_l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1477____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__11;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1477____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1477____closed__1;
x_2 = l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__8;
x_3 = l_Lean_Expr_app___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1477_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1477____closed__2;
x_10 = 1;
x_11 = l_Lean_Elab_Term_evalTerm___rarg(x_9, x_1, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_sequenceMap_loop___at_Mathlib_RunCmd_elabRunElab___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_5);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_3, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_3, x_11);
lean_dec(x_3);
x_13 = lean_array_fget(x_1, x_4);
lean_inc(x_2);
x_14 = lean_apply_1(x_2, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_18 = lean_array_push(x_5, x_16);
x_3 = x_12;
x_4 = x_17;
x_5 = x_18;
goto _start;
}
}
else
{
lean_object* x_20; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_5);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_sequenceMap___at_Mathlib_RunCmd_elabRunElab___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_sequenceMap_loop___at_Mathlib_RunCmd_elabRunElab___spec__2(x_1, x_2, x_3, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Mathlib_RunCmd_elabRunElab___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_7, 5);
lean_inc(x_10);
x_11 = 0;
x_12 = l_Lean_SourceInfo_fromRef(x_10, x_11);
x_13 = lean_st_ref_get(x_8, x_9);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__14;
lean_inc(x_12);
x_16 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__15;
x_18 = l_Lean_Syntax_node2(x_12, x_17, x_16, x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_19 = l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1477_(x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_apply_7(x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_19);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Mathlib_RunCmd_elabRunElab___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Mathlib_RunCmd_elabRunElab___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("doSeqIndent", 11);
return x_1;
}
}
static lean_object* _init_l_Mathlib_RunCmd_elabRunElab___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__1;
x_2 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__1;
x_3 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__2;
x_4 = l_Mathlib_RunCmd_elabRunElab___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Mathlib_RunCmd_elabRunElab___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("doSeqItem", 9);
return x_1;
}
}
static lean_object* _init_l_Mathlib_RunCmd_elabRunElab___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__1;
x_2 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__1;
x_3 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__2;
x_4 = l_Mathlib_RunCmd_elabRunElab___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Mathlib_RunCmd_elabRunElab___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("doExpr", 6);
return x_1;
}
}
static lean_object* _init_l_Mathlib_RunCmd_elabRunElab___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__1;
x_2 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__1;
x_3 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__2;
x_4 = l_Mathlib_RunCmd_elabRunElab___closed__5;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Mathlib_RunCmd_elabRunElab___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("fun", 3);
return x_1;
}
}
static lean_object* _init_l_Mathlib_RunCmd_elabRunElab___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__1;
x_2 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__1;
x_3 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__2;
x_4 = l_Mathlib_RunCmd_elabRunElab___closed__7;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Mathlib_RunCmd_elabRunElab___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("basicFun", 8);
return x_1;
}
}
static lean_object* _init_l_Mathlib_RunCmd_elabRunElab___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__1;
x_2 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__1;
x_3 = l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__2;
x_4 = l_Mathlib_RunCmd_elabRunElab___closed__9;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Mathlib_RunCmd_elabRunElab___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Mathlib_RunCmd_elabRunElab___lambda__2), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Mathlib_RunCmd_elabRunElab(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Mathlib_RunCmd_byElab___closed__2;
lean_inc(x_1);
x_11 = l_Lean_Syntax_isOfKind(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
lean_dec(x_1);
x_15 = l_Mathlib_RunCmd_elabRunElab___closed__2;
lean_inc(x_14);
x_16 = l_Lean_Syntax_isOfKind(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_17 = lean_box(0);
x_18 = l_Mathlib_RunCmd_elabRunElab___lambda__1(x_14, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lean_Syntax_getArg(x_14, x_19);
lean_inc(x_20);
x_21 = l_Lean_Syntax_matchesNull(x_20, x_13);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_20);
lean_dec(x_2);
x_22 = lean_box(0);
x_23 = l_Mathlib_RunCmd_elabRunElab___lambda__1(x_14, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = l_Lean_Syntax_getArg(x_20, x_19);
lean_dec(x_20);
x_25 = l_Mathlib_RunCmd_elabRunElab___closed__4;
lean_inc(x_24);
x_26 = l_Lean_Syntax_isOfKind(x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_24);
lean_dec(x_2);
x_27 = lean_box(0);
x_28 = l_Mathlib_RunCmd_elabRunElab___lambda__1(x_14, x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = l_Lean_Syntax_getArg(x_24, x_19);
x_30 = l_Mathlib_RunCmd_elabRunElab___closed__6;
lean_inc(x_29);
x_31 = l_Lean_Syntax_isOfKind(x_29, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_2);
x_32 = lean_box(0);
x_33 = l_Mathlib_RunCmd_elabRunElab___lambda__1(x_14, x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = l_Lean_Syntax_getArg(x_29, x_19);
lean_dec(x_29);
x_35 = l_Lean_Syntax_getArg(x_24, x_13);
lean_dec(x_24);
x_36 = l_Lean_Syntax_matchesNull(x_35, x_19);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_34);
lean_dec(x_2);
x_37 = lean_box(0);
x_38 = l_Mathlib_RunCmd_elabRunElab___lambda__1(x_14, x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_38;
}
else
{
uint8_t x_39; 
lean_inc(x_34);
x_39 = l_Lean_Syntax_isOfKind(x_34, x_15);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_34);
lean_dec(x_2);
x_40 = lean_box(0);
x_41 = l_Mathlib_RunCmd_elabRunElab___lambda__1(x_14, x_40, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_41;
}
else
{
lean_object* x_42; uint8_t x_43; 
x_42 = l_Lean_Syntax_getArg(x_34, x_19);
lean_inc(x_42);
x_43 = l_Lean_Syntax_matchesNull(x_42, x_13);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_42);
lean_dec(x_34);
lean_dec(x_2);
x_44 = lean_box(0);
x_45 = l_Mathlib_RunCmd_elabRunElab___lambda__1(x_14, x_44, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_45;
}
else
{
lean_object* x_46; uint8_t x_47; 
x_46 = l_Lean_Syntax_getArg(x_42, x_19);
lean_dec(x_42);
lean_inc(x_46);
x_47 = l_Lean_Syntax_isOfKind(x_46, x_25);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_46);
lean_dec(x_34);
lean_dec(x_2);
x_48 = lean_box(0);
x_49 = l_Mathlib_RunCmd_elabRunElab___lambda__1(x_14, x_48, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_49;
}
else
{
lean_object* x_50; uint8_t x_51; 
x_50 = l_Lean_Syntax_getArg(x_46, x_19);
lean_inc(x_50);
x_51 = l_Lean_Syntax_isOfKind(x_50, x_30);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_50);
lean_dec(x_46);
lean_dec(x_34);
lean_dec(x_2);
x_52 = lean_box(0);
x_53 = l_Mathlib_RunCmd_elabRunElab___lambda__1(x_14, x_52, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = l_Lean_Syntax_getArg(x_50, x_19);
lean_dec(x_50);
x_55 = l_Mathlib_RunCmd_elabRunElab___closed__8;
lean_inc(x_54);
x_56 = l_Lean_Syntax_isOfKind(x_54, x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_54);
lean_dec(x_46);
lean_dec(x_34);
lean_dec(x_2);
x_57 = lean_box(0);
x_58 = l_Mathlib_RunCmd_elabRunElab___lambda__1(x_14, x_57, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = l_Lean_Syntax_getArg(x_54, x_13);
lean_dec(x_54);
x_60 = l_Mathlib_RunCmd_elabRunElab___closed__10;
lean_inc(x_59);
x_61 = l_Lean_Syntax_isOfKind(x_59, x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_59);
lean_dec(x_46);
lean_dec(x_34);
lean_dec(x_2);
x_62 = lean_box(0);
x_63 = l_Mathlib_RunCmd_elabRunElab___lambda__1(x_14, x_62, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = l_Lean_Syntax_getArg(x_59, x_19);
x_65 = l_Lean_Syntax_getArgs(x_64);
lean_dec(x_64);
x_66 = l_Mathlib_RunCmd_elabRunElab___closed__11;
x_67 = l_Array_sequenceMap___at_Mathlib_RunCmd_elabRunElab___spec__1(x_65, x_66);
lean_dec(x_65);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_59);
lean_dec(x_46);
lean_dec(x_34);
lean_dec(x_2);
x_68 = lean_box(0);
x_69 = l_Mathlib_RunCmd_elabRunElab___lambda__1(x_14, x_68, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_69;
}
else
{
lean_object* x_70; uint8_t x_71; 
lean_dec(x_67);
x_70 = l_Lean_Syntax_getArg(x_59, x_13);
lean_dec(x_59);
x_71 = l_Lean_Syntax_matchesNull(x_70, x_19);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_46);
lean_dec(x_34);
lean_dec(x_2);
x_72 = lean_box(0);
x_73 = l_Mathlib_RunCmd_elabRunElab___lambda__1(x_14, x_72, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_73;
}
else
{
lean_object* x_74; uint8_t x_75; 
x_74 = l_Lean_Syntax_getArg(x_46, x_13);
lean_dec(x_46);
x_75 = l_Lean_Syntax_matchesNull(x_74, x_19);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_34);
lean_dec(x_2);
x_76 = lean_box(0);
x_77 = l_Mathlib_RunCmd_elabRunElab___lambda__1(x_14, x_76, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_77;
}
else
{
lean_object* x_78; 
lean_dec(x_14);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_78 = l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202_(x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_apply_8(x_79, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_80);
if (lean_obj_tag(x_81) == 0)
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
return x_81;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_81, 0);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_81);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
else
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_81);
if (x_86 == 0)
{
return x_81;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_81, 0);
x_88 = lean_ctor_get(x_81, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_81);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_90 = !lean_is_exclusive(x_78);
if (x_90 == 0)
{
return x_78;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_78, 0);
x_92 = lean_ctor_get(x_78, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_78);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_sequenceMap_loop___at_Mathlib_RunCmd_elabRunElab___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_sequenceMap_loop___at_Mathlib_RunCmd_elabRunElab___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_sequenceMap___at_Mathlib_RunCmd_elabRunElab___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_sequenceMap___at_Mathlib_RunCmd_elabRunElab___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Mathlib_RunCmd_elabRunElab___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Mathlib_RunCmd_elabRunElab___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Eval(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Util_TermUnsafe(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Mathlib_Tactic_RunCmd(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Eval(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Util_TermUnsafe(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Mathlib_RunCmd_runCmd___closed__1 = _init_l_Mathlib_RunCmd_runCmd___closed__1();
lean_mark_persistent(l_Mathlib_RunCmd_runCmd___closed__1);
l_Mathlib_RunCmd_runCmd___closed__2 = _init_l_Mathlib_RunCmd_runCmd___closed__2();
lean_mark_persistent(l_Mathlib_RunCmd_runCmd___closed__2);
l_Mathlib_RunCmd_runCmd___closed__3 = _init_l_Mathlib_RunCmd_runCmd___closed__3();
lean_mark_persistent(l_Mathlib_RunCmd_runCmd___closed__3);
l_Mathlib_RunCmd_runCmd___closed__4 = _init_l_Mathlib_RunCmd_runCmd___closed__4();
lean_mark_persistent(l_Mathlib_RunCmd_runCmd___closed__4);
l_Mathlib_RunCmd_runCmd___closed__5 = _init_l_Mathlib_RunCmd_runCmd___closed__5();
lean_mark_persistent(l_Mathlib_RunCmd_runCmd___closed__5);
l_Mathlib_RunCmd_runCmd___closed__6 = _init_l_Mathlib_RunCmd_runCmd___closed__6();
lean_mark_persistent(l_Mathlib_RunCmd_runCmd___closed__6);
l_Mathlib_RunCmd_runCmd___closed__7 = _init_l_Mathlib_RunCmd_runCmd___closed__7();
lean_mark_persistent(l_Mathlib_RunCmd_runCmd___closed__7);
l_Mathlib_RunCmd_runCmd___closed__8 = _init_l_Mathlib_RunCmd_runCmd___closed__8();
lean_mark_persistent(l_Mathlib_RunCmd_runCmd___closed__8);
l_Mathlib_RunCmd_runCmd___closed__9 = _init_l_Mathlib_RunCmd_runCmd___closed__9();
lean_mark_persistent(l_Mathlib_RunCmd_runCmd___closed__9);
l_Mathlib_RunCmd_runCmd___closed__10 = _init_l_Mathlib_RunCmd_runCmd___closed__10();
lean_mark_persistent(l_Mathlib_RunCmd_runCmd___closed__10);
l_Mathlib_RunCmd_runCmd___closed__11 = _init_l_Mathlib_RunCmd_runCmd___closed__11();
lean_mark_persistent(l_Mathlib_RunCmd_runCmd___closed__11);
l_Mathlib_RunCmd_runCmd___closed__12 = _init_l_Mathlib_RunCmd_runCmd___closed__12();
lean_mark_persistent(l_Mathlib_RunCmd_runCmd___closed__12);
l_Mathlib_RunCmd_runCmd___closed__13 = _init_l_Mathlib_RunCmd_runCmd___closed__13();
lean_mark_persistent(l_Mathlib_RunCmd_runCmd___closed__13);
l_Mathlib_RunCmd_runCmd = _init_l_Mathlib_RunCmd_runCmd();
lean_mark_persistent(l_Mathlib_RunCmd_runCmd);
l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__1 = _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__1();
lean_mark_persistent(l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__1);
l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__2 = _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__2();
lean_mark_persistent(l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__2);
l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__3 = _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__3();
lean_mark_persistent(l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__3);
l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__4 = _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__4();
lean_mark_persistent(l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__4);
l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__5 = _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__5();
lean_mark_persistent(l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__5);
l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__6 = _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__6();
lean_mark_persistent(l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__6);
l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__7 = _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__7();
lean_mark_persistent(l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__7);
l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__8 = _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__8();
lean_mark_persistent(l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__8);
l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__9 = _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__9();
lean_mark_persistent(l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__9);
l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__10 = _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__10();
lean_mark_persistent(l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_203____closed__10);
l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__1 = _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__1();
lean_mark_persistent(l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__1);
l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__2 = _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__2();
lean_mark_persistent(l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__2);
l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__3 = _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__3();
lean_mark_persistent(l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__3);
l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__4 = _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__4();
lean_mark_persistent(l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__4);
l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__5 = _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__5();
lean_mark_persistent(l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__5);
l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__6 = _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__6();
lean_mark_persistent(l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__6);
l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__7 = _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__7();
lean_mark_persistent(l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__7);
l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__8 = _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__8();
lean_mark_persistent(l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__8);
l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__9 = _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__9();
lean_mark_persistent(l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__9);
l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__10 = _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__10();
lean_mark_persistent(l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__10);
l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__11 = _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__11();
lean_mark_persistent(l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__11);
l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__12 = _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__12();
lean_mark_persistent(l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__12);
l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__13 = _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__13();
lean_mark_persistent(l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__13);
l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__14 = _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__14();
lean_mark_persistent(l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__14);
l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__15 = _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__15();
lean_mark_persistent(l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runCmd__1___closed__15);
l_Mathlib_RunCmd_runTac___closed__1 = _init_l_Mathlib_RunCmd_runTac___closed__1();
lean_mark_persistent(l_Mathlib_RunCmd_runTac___closed__1);
l_Mathlib_RunCmd_runTac___closed__2 = _init_l_Mathlib_RunCmd_runTac___closed__2();
lean_mark_persistent(l_Mathlib_RunCmd_runTac___closed__2);
l_Mathlib_RunCmd_runTac___closed__3 = _init_l_Mathlib_RunCmd_runTac___closed__3();
lean_mark_persistent(l_Mathlib_RunCmd_runTac___closed__3);
l_Mathlib_RunCmd_runTac___closed__4 = _init_l_Mathlib_RunCmd_runTac___closed__4();
lean_mark_persistent(l_Mathlib_RunCmd_runTac___closed__4);
l_Mathlib_RunCmd_runTac___closed__5 = _init_l_Mathlib_RunCmd_runTac___closed__5();
lean_mark_persistent(l_Mathlib_RunCmd_runTac___closed__5);
l_Mathlib_RunCmd_runTac___closed__6 = _init_l_Mathlib_RunCmd_runTac___closed__6();
lean_mark_persistent(l_Mathlib_RunCmd_runTac___closed__6);
l_Mathlib_RunCmd_runTac = _init_l_Mathlib_RunCmd_runTac();
lean_mark_persistent(l_Mathlib_RunCmd_runTac);
l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_462____closed__1 = _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_462____closed__1();
lean_mark_persistent(l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_462____closed__1);
l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_462____closed__2 = _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_462____closed__2();
lean_mark_persistent(l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_462____closed__2);
l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_462____closed__3 = _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_462____closed__3();
lean_mark_persistent(l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_462____closed__3);
l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_462____closed__4 = _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_462____closed__4();
lean_mark_persistent(l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_462____closed__4);
l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_462____closed__5 = _init_l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_462____closed__5();
lean_mark_persistent(l_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_462____closed__5);
l_Lean_Elab_throwUnsupportedSyntax___at_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1___spec__1___rarg___closed__1 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1___spec__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1___spec__1___rarg___closed__1);
l_Lean_Elab_throwUnsupportedSyntax___at_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1___spec__1___rarg___closed__2 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1___spec__1___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Mathlib_RunCmd___aux__Mathlib__Tactic__RunCmd______elabRules__Mathlib__RunCmd__runTac__1___spec__1___rarg___closed__2);
l_Mathlib_RunCmd_byElab___closed__1 = _init_l_Mathlib_RunCmd_byElab___closed__1();
lean_mark_persistent(l_Mathlib_RunCmd_byElab___closed__1);
l_Mathlib_RunCmd_byElab___closed__2 = _init_l_Mathlib_RunCmd_byElab___closed__2();
lean_mark_persistent(l_Mathlib_RunCmd_byElab___closed__2);
l_Mathlib_RunCmd_byElab___closed__3 = _init_l_Mathlib_RunCmd_byElab___closed__3();
lean_mark_persistent(l_Mathlib_RunCmd_byElab___closed__3);
l_Mathlib_RunCmd_byElab___closed__4 = _init_l_Mathlib_RunCmd_byElab___closed__4();
lean_mark_persistent(l_Mathlib_RunCmd_byElab___closed__4);
l_Mathlib_RunCmd_byElab___closed__5 = _init_l_Mathlib_RunCmd_byElab___closed__5();
lean_mark_persistent(l_Mathlib_RunCmd_byElab___closed__5);
l_Mathlib_RunCmd_byElab___closed__6 = _init_l_Mathlib_RunCmd_byElab___closed__6();
lean_mark_persistent(l_Mathlib_RunCmd_byElab___closed__6);
l_Mathlib_RunCmd_byElab = _init_l_Mathlib_RunCmd_byElab();
lean_mark_persistent(l_Mathlib_RunCmd_byElab);
l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__1 = _init_l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__1();
lean_mark_persistent(l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__1);
l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__2 = _init_l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__2();
lean_mark_persistent(l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__2);
l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__3 = _init_l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__3();
lean_mark_persistent(l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__3);
l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__4 = _init_l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__4();
lean_mark_persistent(l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__4);
l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__5 = _init_l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__5();
lean_mark_persistent(l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__5);
l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__6 = _init_l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__6();
lean_mark_persistent(l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__6);
l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__7 = _init_l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__7();
lean_mark_persistent(l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__7);
l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__8 = _init_l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__8();
lean_mark_persistent(l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__8);
l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__9 = _init_l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__9();
lean_mark_persistent(l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__9);
l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__10 = _init_l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__10();
lean_mark_persistent(l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__10);
l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__11 = _init_l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__11();
lean_mark_persistent(l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__11);
l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__12 = _init_l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__12();
lean_mark_persistent(l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__12);
l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__13 = _init_l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__13();
lean_mark_persistent(l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__13);
l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__14 = _init_l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__14();
lean_mark_persistent(l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1202____closed__14);
l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1477____closed__1 = _init_l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1477____closed__1();
lean_mark_persistent(l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1477____closed__1);
l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1477____closed__2 = _init_l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1477____closed__2();
lean_mark_persistent(l_Mathlib_RunCmd_elabRunElab_unsafe____x40_Mathlib_Tactic_RunCmd___hyg_1477____closed__2);
l_Mathlib_RunCmd_elabRunElab___closed__1 = _init_l_Mathlib_RunCmd_elabRunElab___closed__1();
lean_mark_persistent(l_Mathlib_RunCmd_elabRunElab___closed__1);
l_Mathlib_RunCmd_elabRunElab___closed__2 = _init_l_Mathlib_RunCmd_elabRunElab___closed__2();
lean_mark_persistent(l_Mathlib_RunCmd_elabRunElab___closed__2);
l_Mathlib_RunCmd_elabRunElab___closed__3 = _init_l_Mathlib_RunCmd_elabRunElab___closed__3();
lean_mark_persistent(l_Mathlib_RunCmd_elabRunElab___closed__3);
l_Mathlib_RunCmd_elabRunElab___closed__4 = _init_l_Mathlib_RunCmd_elabRunElab___closed__4();
lean_mark_persistent(l_Mathlib_RunCmd_elabRunElab___closed__4);
l_Mathlib_RunCmd_elabRunElab___closed__5 = _init_l_Mathlib_RunCmd_elabRunElab___closed__5();
lean_mark_persistent(l_Mathlib_RunCmd_elabRunElab___closed__5);
l_Mathlib_RunCmd_elabRunElab___closed__6 = _init_l_Mathlib_RunCmd_elabRunElab___closed__6();
lean_mark_persistent(l_Mathlib_RunCmd_elabRunElab___closed__6);
l_Mathlib_RunCmd_elabRunElab___closed__7 = _init_l_Mathlib_RunCmd_elabRunElab___closed__7();
lean_mark_persistent(l_Mathlib_RunCmd_elabRunElab___closed__7);
l_Mathlib_RunCmd_elabRunElab___closed__8 = _init_l_Mathlib_RunCmd_elabRunElab___closed__8();
lean_mark_persistent(l_Mathlib_RunCmd_elabRunElab___closed__8);
l_Mathlib_RunCmd_elabRunElab___closed__9 = _init_l_Mathlib_RunCmd_elabRunElab___closed__9();
lean_mark_persistent(l_Mathlib_RunCmd_elabRunElab___closed__9);
l_Mathlib_RunCmd_elabRunElab___closed__10 = _init_l_Mathlib_RunCmd_elabRunElab___closed__10();
lean_mark_persistent(l_Mathlib_RunCmd_elabRunElab___closed__10);
l_Mathlib_RunCmd_elabRunElab___closed__11 = _init_l_Mathlib_RunCmd_elabRunElab___closed__11();
lean_mark_persistent(l_Mathlib_RunCmd_elabRunElab___closed__11);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
