// Lean compiler output
// Module: Mathlib.Tactic.ApplyWith
// Imports: Init Lean Std.Util.TermUnsafe
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Mathlib_Tactic_applyWith___closed__6;
static lean_object* l_Mathlib_Tactic_applyWith___closed__14;
static lean_object* l_Mathlib_Tactic_applyWith___closed__8;
static lean_object* l_Mathlib_Tactic_applyWith___closed__9;
static lean_object* l_Mathlib_Tactic_applyWith___closed__12;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
static lean_object* l_Mathlib_Tactic_applyWith___closed__17;
static lean_object* l_Mathlib_Tactic_applyWith___closed__7;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Mathlib_Tactic_applyWith___closed__3;
static lean_object* l_Mathlib_Tactic_applyWith___closed__5;
static lean_object* l_Mathlib_Tactic___aux__Mathlib__Tactic__ApplyWith______elabRules__Mathlib__Tactic__applyWith__1_unsafe____x40_Mathlib_Tactic_ApplyWith___hyg_212____closed__2;
LEAN_EXPORT lean_object* l_Mathlib_Tactic___aux__Mathlib__Tactic__ApplyWith______elabRules__Mathlib__Tactic__applyWith__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Mathlib_Tactic_applyWith___closed__24;
static lean_object* l_Mathlib_Tactic_applyWith___closed__16;
LEAN_EXPORT lean_object* l_Mathlib_Tactic___aux__Mathlib__Tactic__ApplyWith______elabRules__Mathlib__Tactic__applyWith__1_unsafe____x40_Mathlib_Tactic_ApplyWith___hyg_212_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_Mathlib_Tactic_applyWith___closed__11;
static lean_object* l_Mathlib_Tactic___aux__Mathlib__Tactic__ApplyWith______elabRules__Mathlib__Tactic__applyWith__1_unsafe____x40_Mathlib_Tactic_ApplyWith___hyg_212____closed__3;
static lean_object* l_Mathlib_Tactic_applyWith___closed__20;
static lean_object* l_Mathlib_Tactic_applyWith___closed__13;
static lean_object* l_Mathlib_Tactic___aux__Mathlib__Tactic__ApplyWith______elabRules__Mathlib__Tactic__applyWith__1_unsafe____x40_Mathlib_Tactic_ApplyWith___hyg_212____closed__4;
static lean_object* l_Mathlib_Tactic_applyWith___closed__25;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___spec__1___rarg(lean_object*);
static lean_object* l_Mathlib_Tactic___aux__Mathlib__Tactic__ApplyWith______elabRules__Mathlib__Tactic__applyWith__1_unsafe____x40_Mathlib_Tactic_ApplyWith___hyg_212____closed__5;
static lean_object* l_Mathlib_Tactic_applyWith___closed__26;
static lean_object* l_Mathlib_Tactic_applyWith___closed__2;
static lean_object* l_Mathlib_Tactic_applyWith___closed__15;
static lean_object* l_Mathlib_Tactic___aux__Mathlib__Tactic__ApplyWith______elabRules__Mathlib__Tactic__applyWith__1_unsafe____x40_Mathlib_Tactic_ApplyWith___hyg_212____closed__1;
lean_object* l_Lean_MVarId_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Mathlib_Tactic_applyWith___closed__23;
LEAN_EXPORT lean_object* l_Mathlib_Tactic_applyWith;
static lean_object* l_Mathlib_Tactic_applyWith___closed__10;
lean_object* l_Lean_Elab_Term_evalTerm___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Mathlib_Tactic_applyWith___closed__22;
static lean_object* l_Mathlib_Tactic_applyWith___closed__18;
static lean_object* l_Mathlib_Tactic_applyWith___closed__1;
LEAN_EXPORT lean_object* l_Mathlib_Tactic___aux__Mathlib__Tactic__ApplyWith______elabRules__Mathlib__Tactic__applyWith__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Mathlib_Tactic_applyWith___closed__4;
static lean_object* l_Mathlib_Tactic_applyWith___closed__19;
lean_object* l_Lean_Elab_Tactic_evalApplyLikeTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Mathlib_Tactic_applyWith___closed__21;
static lean_object* _init_l_Mathlib_Tactic_applyWith___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Mathlib", 7);
return x_1;
}
}
static lean_object* _init_l_Mathlib_Tactic_applyWith___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Tactic", 6);
return x_1;
}
}
static lean_object* _init_l_Mathlib_Tactic_applyWith___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("applyWith", 9);
return x_1;
}
}
static lean_object* _init_l_Mathlib_Tactic_applyWith___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Mathlib_Tactic_applyWith___closed__1;
x_2 = l_Mathlib_Tactic_applyWith___closed__2;
x_3 = l_Mathlib_Tactic_applyWith___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Mathlib_Tactic_applyWith___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("andthen", 7);
return x_1;
}
}
static lean_object* _init_l_Mathlib_Tactic_applyWith___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Mathlib_Tactic_applyWith___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Mathlib_Tactic_applyWith___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("apply", 5);
return x_1;
}
}
static lean_object* _init_l_Mathlib_Tactic_applyWith___closed__8() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Mathlib_Tactic_applyWith___closed__7;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Mathlib_Tactic_applyWith___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" (", 2);
return x_1;
}
}
static lean_object* _init_l_Mathlib_Tactic_applyWith___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Mathlib_Tactic_applyWith___closed__9;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Mathlib_Tactic_applyWith___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Mathlib_Tactic_applyWith___closed__6;
x_2 = l_Mathlib_Tactic_applyWith___closed__8;
x_3 = l_Mathlib_Tactic_applyWith___closed__10;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Mathlib_Tactic_applyWith___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("config", 6);
return x_1;
}
}
static lean_object* _init_l_Mathlib_Tactic_applyWith___closed__13() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Mathlib_Tactic_applyWith___closed__12;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Mathlib_Tactic_applyWith___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Mathlib_Tactic_applyWith___closed__6;
x_2 = l_Mathlib_Tactic_applyWith___closed__11;
x_3 = l_Mathlib_Tactic_applyWith___closed__13;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Mathlib_Tactic_applyWith___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" := ", 4);
return x_1;
}
}
static lean_object* _init_l_Mathlib_Tactic_applyWith___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Mathlib_Tactic_applyWith___closed__15;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Mathlib_Tactic_applyWith___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Mathlib_Tactic_applyWith___closed__6;
x_2 = l_Mathlib_Tactic_applyWith___closed__14;
x_3 = l_Mathlib_Tactic_applyWith___closed__16;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Mathlib_Tactic_applyWith___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("term", 4);
return x_1;
}
}
static lean_object* _init_l_Mathlib_Tactic_applyWith___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Mathlib_Tactic_applyWith___closed__18;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Mathlib_Tactic_applyWith___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Mathlib_Tactic_applyWith___closed__19;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Mathlib_Tactic_applyWith___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Mathlib_Tactic_applyWith___closed__6;
x_2 = l_Mathlib_Tactic_applyWith___closed__17;
x_3 = l_Mathlib_Tactic_applyWith___closed__20;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Mathlib_Tactic_applyWith___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(") ", 2);
return x_1;
}
}
static lean_object* _init_l_Mathlib_Tactic_applyWith___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Mathlib_Tactic_applyWith___closed__22;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Mathlib_Tactic_applyWith___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Mathlib_Tactic_applyWith___closed__6;
x_2 = l_Mathlib_Tactic_applyWith___closed__21;
x_3 = l_Mathlib_Tactic_applyWith___closed__23;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Mathlib_Tactic_applyWith___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Mathlib_Tactic_applyWith___closed__6;
x_2 = l_Mathlib_Tactic_applyWith___closed__24;
x_3 = l_Mathlib_Tactic_applyWith___closed__20;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Mathlib_Tactic_applyWith___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Mathlib_Tactic_applyWith___closed__4;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Mathlib_Tactic_applyWith___closed__25;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Mathlib_Tactic_applyWith() {
_start:
{
lean_object* x_1; 
x_1 = l_Mathlib_Tactic_applyWith___closed__26;
return x_1;
}
}
static lean_object* _init_l_Mathlib_Tactic___aux__Mathlib__Tactic__ApplyWith______elabRules__Mathlib__Tactic__applyWith__1_unsafe____x40_Mathlib_Tactic_ApplyWith___hyg_212____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Mathlib_Tactic___aux__Mathlib__Tactic__ApplyWith______elabRules__Mathlib__Tactic__applyWith__1_unsafe____x40_Mathlib_Tactic_ApplyWith___hyg_212____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Meta", 4);
return x_1;
}
}
static lean_object* _init_l_Mathlib_Tactic___aux__Mathlib__Tactic__ApplyWith______elabRules__Mathlib__Tactic__applyWith__1_unsafe____x40_Mathlib_Tactic_ApplyWith___hyg_212____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ApplyConfig", 11);
return x_1;
}
}
static lean_object* _init_l_Mathlib_Tactic___aux__Mathlib__Tactic__ApplyWith______elabRules__Mathlib__Tactic__applyWith__1_unsafe____x40_Mathlib_Tactic_ApplyWith___hyg_212____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Mathlib_Tactic___aux__Mathlib__Tactic__ApplyWith______elabRules__Mathlib__Tactic__applyWith__1_unsafe____x40_Mathlib_Tactic_ApplyWith___hyg_212____closed__1;
x_2 = l_Mathlib_Tactic___aux__Mathlib__Tactic__ApplyWith______elabRules__Mathlib__Tactic__applyWith__1_unsafe____x40_Mathlib_Tactic_ApplyWith___hyg_212____closed__2;
x_3 = l_Mathlib_Tactic___aux__Mathlib__Tactic__ApplyWith______elabRules__Mathlib__Tactic__applyWith__1_unsafe____x40_Mathlib_Tactic_ApplyWith___hyg_212____closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Mathlib_Tactic___aux__Mathlib__Tactic__ApplyWith______elabRules__Mathlib__Tactic__applyWith__1_unsafe____x40_Mathlib_Tactic_ApplyWith___hyg_212____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Mathlib_Tactic___aux__Mathlib__Tactic__ApplyWith______elabRules__Mathlib__Tactic__applyWith__1_unsafe____x40_Mathlib_Tactic_ApplyWith___hyg_212____closed__4;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Mathlib_Tactic___aux__Mathlib__Tactic__ApplyWith______elabRules__Mathlib__Tactic__applyWith__1_unsafe____x40_Mathlib_Tactic_ApplyWith___hyg_212_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = l_Mathlib_Tactic___aux__Mathlib__Tactic__ApplyWith______elabRules__Mathlib__Tactic__applyWith__1_unsafe____x40_Mathlib_Tactic_ApplyWith___hyg_212____closed__5;
x_10 = 1;
x_11 = l_Lean_Elab_Term_evalTerm___rarg(x_9, x_1, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Mathlib_Tactic___aux__Mathlib__Tactic__ApplyWith______elabRules__Mathlib__Tactic__applyWith__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_apply(x_2, x_3, x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Mathlib_Tactic___aux__Mathlib__Tactic__ApplyWith______elabRules__Mathlib__Tactic__applyWith__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Mathlib_Tactic_applyWith___closed__4;
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
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___spec__1___rarg(x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_unsigned_to_nat(4u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = lean_unsigned_to_nat(6u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
lean_dec(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_18 = l_Mathlib_Tactic___aux__Mathlib__Tactic__ApplyWith______elabRules__Mathlib__Tactic__applyWith__1_unsafe____x40_Mathlib_Tactic_ApplyWith___hyg_212_(x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_closure((void*)(l_Mathlib_Tactic___aux__Mathlib__Tactic__ApplyWith______elabRules__Mathlib__Tactic__applyWith__1___lambda__1), 8, 1);
lean_closure_set(x_21, 0, x_19);
x_22 = l_Lean_Elab_Tactic_evalApplyLikeTactic(x_21, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_18, 0);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_18);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Util_TermUnsafe(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Mathlib_Tactic_ApplyWith(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Util_TermUnsafe(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Mathlib_Tactic_applyWith___closed__1 = _init_l_Mathlib_Tactic_applyWith___closed__1();
lean_mark_persistent(l_Mathlib_Tactic_applyWith___closed__1);
l_Mathlib_Tactic_applyWith___closed__2 = _init_l_Mathlib_Tactic_applyWith___closed__2();
lean_mark_persistent(l_Mathlib_Tactic_applyWith___closed__2);
l_Mathlib_Tactic_applyWith___closed__3 = _init_l_Mathlib_Tactic_applyWith___closed__3();
lean_mark_persistent(l_Mathlib_Tactic_applyWith___closed__3);
l_Mathlib_Tactic_applyWith___closed__4 = _init_l_Mathlib_Tactic_applyWith___closed__4();
lean_mark_persistent(l_Mathlib_Tactic_applyWith___closed__4);
l_Mathlib_Tactic_applyWith___closed__5 = _init_l_Mathlib_Tactic_applyWith___closed__5();
lean_mark_persistent(l_Mathlib_Tactic_applyWith___closed__5);
l_Mathlib_Tactic_applyWith___closed__6 = _init_l_Mathlib_Tactic_applyWith___closed__6();
lean_mark_persistent(l_Mathlib_Tactic_applyWith___closed__6);
l_Mathlib_Tactic_applyWith___closed__7 = _init_l_Mathlib_Tactic_applyWith___closed__7();
lean_mark_persistent(l_Mathlib_Tactic_applyWith___closed__7);
l_Mathlib_Tactic_applyWith___closed__8 = _init_l_Mathlib_Tactic_applyWith___closed__8();
lean_mark_persistent(l_Mathlib_Tactic_applyWith___closed__8);
l_Mathlib_Tactic_applyWith___closed__9 = _init_l_Mathlib_Tactic_applyWith___closed__9();
lean_mark_persistent(l_Mathlib_Tactic_applyWith___closed__9);
l_Mathlib_Tactic_applyWith___closed__10 = _init_l_Mathlib_Tactic_applyWith___closed__10();
lean_mark_persistent(l_Mathlib_Tactic_applyWith___closed__10);
l_Mathlib_Tactic_applyWith___closed__11 = _init_l_Mathlib_Tactic_applyWith___closed__11();
lean_mark_persistent(l_Mathlib_Tactic_applyWith___closed__11);
l_Mathlib_Tactic_applyWith___closed__12 = _init_l_Mathlib_Tactic_applyWith___closed__12();
lean_mark_persistent(l_Mathlib_Tactic_applyWith___closed__12);
l_Mathlib_Tactic_applyWith___closed__13 = _init_l_Mathlib_Tactic_applyWith___closed__13();
lean_mark_persistent(l_Mathlib_Tactic_applyWith___closed__13);
l_Mathlib_Tactic_applyWith___closed__14 = _init_l_Mathlib_Tactic_applyWith___closed__14();
lean_mark_persistent(l_Mathlib_Tactic_applyWith___closed__14);
l_Mathlib_Tactic_applyWith___closed__15 = _init_l_Mathlib_Tactic_applyWith___closed__15();
lean_mark_persistent(l_Mathlib_Tactic_applyWith___closed__15);
l_Mathlib_Tactic_applyWith___closed__16 = _init_l_Mathlib_Tactic_applyWith___closed__16();
lean_mark_persistent(l_Mathlib_Tactic_applyWith___closed__16);
l_Mathlib_Tactic_applyWith___closed__17 = _init_l_Mathlib_Tactic_applyWith___closed__17();
lean_mark_persistent(l_Mathlib_Tactic_applyWith___closed__17);
l_Mathlib_Tactic_applyWith___closed__18 = _init_l_Mathlib_Tactic_applyWith___closed__18();
lean_mark_persistent(l_Mathlib_Tactic_applyWith___closed__18);
l_Mathlib_Tactic_applyWith___closed__19 = _init_l_Mathlib_Tactic_applyWith___closed__19();
lean_mark_persistent(l_Mathlib_Tactic_applyWith___closed__19);
l_Mathlib_Tactic_applyWith___closed__20 = _init_l_Mathlib_Tactic_applyWith___closed__20();
lean_mark_persistent(l_Mathlib_Tactic_applyWith___closed__20);
l_Mathlib_Tactic_applyWith___closed__21 = _init_l_Mathlib_Tactic_applyWith___closed__21();
lean_mark_persistent(l_Mathlib_Tactic_applyWith___closed__21);
l_Mathlib_Tactic_applyWith___closed__22 = _init_l_Mathlib_Tactic_applyWith___closed__22();
lean_mark_persistent(l_Mathlib_Tactic_applyWith___closed__22);
l_Mathlib_Tactic_applyWith___closed__23 = _init_l_Mathlib_Tactic_applyWith___closed__23();
lean_mark_persistent(l_Mathlib_Tactic_applyWith___closed__23);
l_Mathlib_Tactic_applyWith___closed__24 = _init_l_Mathlib_Tactic_applyWith___closed__24();
lean_mark_persistent(l_Mathlib_Tactic_applyWith___closed__24);
l_Mathlib_Tactic_applyWith___closed__25 = _init_l_Mathlib_Tactic_applyWith___closed__25();
lean_mark_persistent(l_Mathlib_Tactic_applyWith___closed__25);
l_Mathlib_Tactic_applyWith___closed__26 = _init_l_Mathlib_Tactic_applyWith___closed__26();
lean_mark_persistent(l_Mathlib_Tactic_applyWith___closed__26);
l_Mathlib_Tactic_applyWith = _init_l_Mathlib_Tactic_applyWith();
lean_mark_persistent(l_Mathlib_Tactic_applyWith);
l_Mathlib_Tactic___aux__Mathlib__Tactic__ApplyWith______elabRules__Mathlib__Tactic__applyWith__1_unsafe____x40_Mathlib_Tactic_ApplyWith___hyg_212____closed__1 = _init_l_Mathlib_Tactic___aux__Mathlib__Tactic__ApplyWith______elabRules__Mathlib__Tactic__applyWith__1_unsafe____x40_Mathlib_Tactic_ApplyWith___hyg_212____closed__1();
lean_mark_persistent(l_Mathlib_Tactic___aux__Mathlib__Tactic__ApplyWith______elabRules__Mathlib__Tactic__applyWith__1_unsafe____x40_Mathlib_Tactic_ApplyWith___hyg_212____closed__1);
l_Mathlib_Tactic___aux__Mathlib__Tactic__ApplyWith______elabRules__Mathlib__Tactic__applyWith__1_unsafe____x40_Mathlib_Tactic_ApplyWith___hyg_212____closed__2 = _init_l_Mathlib_Tactic___aux__Mathlib__Tactic__ApplyWith______elabRules__Mathlib__Tactic__applyWith__1_unsafe____x40_Mathlib_Tactic_ApplyWith___hyg_212____closed__2();
lean_mark_persistent(l_Mathlib_Tactic___aux__Mathlib__Tactic__ApplyWith______elabRules__Mathlib__Tactic__applyWith__1_unsafe____x40_Mathlib_Tactic_ApplyWith___hyg_212____closed__2);
l_Mathlib_Tactic___aux__Mathlib__Tactic__ApplyWith______elabRules__Mathlib__Tactic__applyWith__1_unsafe____x40_Mathlib_Tactic_ApplyWith___hyg_212____closed__3 = _init_l_Mathlib_Tactic___aux__Mathlib__Tactic__ApplyWith______elabRules__Mathlib__Tactic__applyWith__1_unsafe____x40_Mathlib_Tactic_ApplyWith___hyg_212____closed__3();
lean_mark_persistent(l_Mathlib_Tactic___aux__Mathlib__Tactic__ApplyWith______elabRules__Mathlib__Tactic__applyWith__1_unsafe____x40_Mathlib_Tactic_ApplyWith___hyg_212____closed__3);
l_Mathlib_Tactic___aux__Mathlib__Tactic__ApplyWith______elabRules__Mathlib__Tactic__applyWith__1_unsafe____x40_Mathlib_Tactic_ApplyWith___hyg_212____closed__4 = _init_l_Mathlib_Tactic___aux__Mathlib__Tactic__ApplyWith______elabRules__Mathlib__Tactic__applyWith__1_unsafe____x40_Mathlib_Tactic_ApplyWith___hyg_212____closed__4();
lean_mark_persistent(l_Mathlib_Tactic___aux__Mathlib__Tactic__ApplyWith______elabRules__Mathlib__Tactic__applyWith__1_unsafe____x40_Mathlib_Tactic_ApplyWith___hyg_212____closed__4);
l_Mathlib_Tactic___aux__Mathlib__Tactic__ApplyWith______elabRules__Mathlib__Tactic__applyWith__1_unsafe____x40_Mathlib_Tactic_ApplyWith___hyg_212____closed__5 = _init_l_Mathlib_Tactic___aux__Mathlib__Tactic__ApplyWith______elabRules__Mathlib__Tactic__applyWith__1_unsafe____x40_Mathlib_Tactic_ApplyWith___hyg_212____closed__5();
lean_mark_persistent(l_Mathlib_Tactic___aux__Mathlib__Tactic__ApplyWith______elabRules__Mathlib__Tactic__applyWith__1_unsafe____x40_Mathlib_Tactic_ApplyWith___hyg_212____closed__5);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
