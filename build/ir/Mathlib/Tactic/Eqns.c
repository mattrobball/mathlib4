// Lean compiler output
// Module: Mathlib.Tactic.Eqns
// Imports: Init Lean.Meta.Eqns Mathlib.Lean.Expr Std.Lean.NameMapAttribute
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Std_Tactic_Lint_initFn____x40_Std_Tactic_Lint_Basic___hyg_1609____spec__1___rarg(lean_object*);
LEAN_EXPORT lean_object* l_initFn____x40_Mathlib_Tactic_Eqns___hyg_36_(lean_object*);
static lean_object* l_initFn____x40_Mathlib_Tactic_Eqns___hyg_36____closed__1;
static lean_object* l_eqns___closed__7;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Array_sequenceMap___at_Std_Tactic_Lint_initFn____x40_Std_Tactic_Lint_Basic___hyg_1609____spec__2(lean_object*, lean_object*);
static lean_object* l_eqns___closed__11;
LEAN_EXPORT lean_object* l_eqnsAttribute;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
static lean_object* l_eqns___closed__16;
lean_object* l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at_Lean_initFn____x40_Lean_Elab_InheritDoc___hyg_4____spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_initFn____x40_Mathlib_Tactic_Eqns___hyg_36____lambda__1(lean_object*);
lean_object* l_Lean_registerNameMapAttribute___rarg(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_eqns___closed__9;
LEAN_EXPORT lean_object* l_initFn____x40_Mathlib_Tactic_Eqns___hyg_36____lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_eqns___closed__14;
static lean_object* l_initFn____x40_Mathlib_Tactic_Eqns___hyg_36____lambda__2___closed__1;
static lean_object* l_eqns___closed__10;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_initFn____x40_Mathlib_Tactic_Eqns___hyg_259____closed__1;
static lean_object* l_eqns___closed__6;
LEAN_EXPORT lean_object* l_initFn____x40_Mathlib_Tactic_Eqns___hyg_259____lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_eqns___closed__13;
static lean_object* l_eqns___closed__5;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_eqns___closed__12;
LEAN_EXPORT lean_object* l_initFn____x40_Mathlib_Tactic_Eqns___hyg_259_(lean_object*);
static lean_object* l_eqns___closed__2;
lean_object* l_Lean_NameMapExtension_find_x3f___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_eqns___closed__15;
static lean_object* l_initFn____x40_Mathlib_Tactic_Eqns___hyg_259____lambda__1___closed__1;
lean_object* l_Lean_Meta_registerGetEqnsFn(lean_object*, lean_object*);
static lean_object* l_initFn____x40_Mathlib_Tactic_Eqns___hyg_36____closed__2;
static lean_object* l_eqns___closed__8;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_initFn____x40_Mathlib_Tactic_Eqns___hyg_259____lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_eqns___closed__17;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_initFn____x40_Mathlib_Tactic_Eqns___hyg_36____spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_eqns___closed__1;
static lean_object* l_eqns___closed__3;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_eqns;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_initFn____x40_Mathlib_Tactic_Eqns___hyg_36____spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_initFn____x40_Mathlib_Tactic_Eqns___hyg_36____closed__3;
static lean_object* l_eqns___closed__4;
static lean_object* _init_l_eqns___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("eqns", 4);
return x_1;
}
}
static lean_object* _init_l_eqns___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_eqns___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_eqns___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("andthen", 7);
return x_1;
}
}
static lean_object* _init_l_eqns___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_eqns___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_eqns___closed__5() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_eqns___closed__1;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_eqns___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("many", 4);
return x_1;
}
}
static lean_object* _init_l_eqns___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_eqns___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_eqns___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ppSpace", 7);
return x_1;
}
}
static lean_object* _init_l_eqns___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_eqns___closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_eqns___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_eqns___closed__9;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_eqns___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ident", 5);
return x_1;
}
}
static lean_object* _init_l_eqns___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_eqns___closed__11;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_eqns___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_eqns___closed__12;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_eqns___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_eqns___closed__4;
x_2 = l_eqns___closed__10;
x_3 = l_eqns___closed__13;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_eqns___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_eqns___closed__7;
x_2 = l_eqns___closed__14;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_eqns___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_eqns___closed__4;
x_2 = l_eqns___closed__5;
x_3 = l_eqns___closed__15;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_eqns___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_eqns___closed__2;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_eqns___closed__16;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_eqns() {
_start:
{
lean_object* x_1; 
x_1 = l_eqns___closed__17;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_initFn____x40_Mathlib_Tactic_Eqns___hyg_36____spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_2, x_1);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_array_uget(x_3, x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_uset(x_3, x_2, x_10);
x_12 = lean_box(0);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at_Lean_initFn____x40_Lean_Elab_InheritDoc___hyg_4____spec__1(x_9, x_12, x_4, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_18 = lean_array_uset(x_11, x_2, x_14);
x_2 = x_17;
x_3 = x_18;
x_6 = x_15;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_13);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l_initFn____x40_Mathlib_Tactic_Eqns___hyg_36____lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_initFn____x40_Mathlib_Tactic_Eqns___hyg_36____lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_initFn____x40_Mathlib_Tactic_Eqns___hyg_36____lambda__1), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_initFn____x40_Mathlib_Tactic_Eqns___hyg_36____lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
lean_dec(x_2);
lean_inc(x_3);
x_7 = l_Lean_Syntax_isOfKind(x_3, x_1);
lean_dec(x_1);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = l_Lean_Elab_throwUnsupportedSyntax___at_Std_Tactic_Lint_initFn____x40_Std_Tactic_Lint_Basic___hyg_1609____spec__1___rarg(x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_3, x_9);
lean_dec(x_3);
x_11 = l_Lean_Syntax_getArgs(x_10);
lean_dec(x_10);
x_12 = l_initFn____x40_Mathlib_Tactic_Eqns___hyg_36____lambda__2___closed__1;
x_13 = l_Array_sequenceMap___at_Std_Tactic_Lint_initFn____x40_Std_Tactic_Lint_Basic___hyg_1609____spec__2(x_11, x_12);
lean_dec(x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
x_14 = l_Lean_Elab_throwUnsupportedSyntax___at_Std_Tactic_Lint_initFn____x40_Std_Tactic_Lint_Basic___hyg_1609____spec__1___rarg(x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_array_get_size(x_15);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
x_19 = l_Array_mapMUnsafe_map___at_initFn____x40_Mathlib_Tactic_Eqns___hyg_36____spec__1(x_17, x_18, x_15, x_4, x_5, x_6);
return x_19;
}
}
}
}
static lean_object* _init_l_initFn____x40_Mathlib_Tactic_Eqns___hyg_36____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("eqnsAttribute", 13);
return x_1;
}
}
static lean_object* _init_l_initFn____x40_Mathlib_Tactic_Eqns___hyg_36____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_initFn____x40_Mathlib_Tactic_Eqns___hyg_36____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_initFn____x40_Mathlib_Tactic_Eqns___hyg_36____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Overrides the equation lemmas for a declaration to the provided list", 68);
return x_1;
}
}
LEAN_EXPORT lean_object* l_initFn____x40_Mathlib_Tactic_Eqns___hyg_36_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_eqns___closed__2;
x_3 = lean_alloc_closure((void*)(l_initFn____x40_Mathlib_Tactic_Eqns___hyg_36____lambda__2), 6, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_initFn____x40_Mathlib_Tactic_Eqns___hyg_36____closed__2;
x_5 = l_initFn____x40_Mathlib_Tactic_Eqns___hyg_36____closed__3;
x_6 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
lean_ctor_set(x_6, 3, x_3);
x_7 = l_Lean_registerNameMapAttribute___rarg(x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_initFn____x40_Mathlib_Tactic_Eqns___hyg_36____spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l_Array_mapMUnsafe_map___at_initFn____x40_Mathlib_Tactic_Eqns___hyg_36____spec__1(x_7, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
static lean_object* _init_l_initFn____x40_Mathlib_Tactic_Eqns___hyg_259____lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_eqnsAttribute;
return x_1;
}
}
LEAN_EXPORT lean_object* l_initFn____x40_Mathlib_Tactic_Eqns___hyg_259____lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_initFn____x40_Mathlib_Tactic_Eqns___hyg_259____lambda__1___closed__1;
x_12 = l_Lean_NameMapExtension_find_x3f___rarg(x_11, x_10, x_1);
lean_dec(x_10);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_7);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_initFn____x40_Mathlib_Tactic_Eqns___hyg_259____lambda__1___closed__1;
x_17 = l_Lean_NameMapExtension_find_x3f___rarg(x_16, x_15, x_1);
lean_dec(x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
}
}
static lean_object* _init_l_initFn____x40_Mathlib_Tactic_Eqns___hyg_259____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_initFn____x40_Mathlib_Tactic_Eqns___hyg_259____lambda__1___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_initFn____x40_Mathlib_Tactic_Eqns___hyg_259_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_initFn____x40_Mathlib_Tactic_Eqns___hyg_259____closed__1;
x_3 = l_Lean_Meta_registerGetEqnsFn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_initFn____x40_Mathlib_Tactic_Eqns___hyg_259____lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_initFn____x40_Mathlib_Tactic_Eqns___hyg_259____lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Eqns(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Lean_Expr(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Lean_NameMapAttribute(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Mathlib_Tactic_Eqns(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Eqns(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Lean_NameMapAttribute(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_eqns___closed__1 = _init_l_eqns___closed__1();
lean_mark_persistent(l_eqns___closed__1);
l_eqns___closed__2 = _init_l_eqns___closed__2();
lean_mark_persistent(l_eqns___closed__2);
l_eqns___closed__3 = _init_l_eqns___closed__3();
lean_mark_persistent(l_eqns___closed__3);
l_eqns___closed__4 = _init_l_eqns___closed__4();
lean_mark_persistent(l_eqns___closed__4);
l_eqns___closed__5 = _init_l_eqns___closed__5();
lean_mark_persistent(l_eqns___closed__5);
l_eqns___closed__6 = _init_l_eqns___closed__6();
lean_mark_persistent(l_eqns___closed__6);
l_eqns___closed__7 = _init_l_eqns___closed__7();
lean_mark_persistent(l_eqns___closed__7);
l_eqns___closed__8 = _init_l_eqns___closed__8();
lean_mark_persistent(l_eqns___closed__8);
l_eqns___closed__9 = _init_l_eqns___closed__9();
lean_mark_persistent(l_eqns___closed__9);
l_eqns___closed__10 = _init_l_eqns___closed__10();
lean_mark_persistent(l_eqns___closed__10);
l_eqns___closed__11 = _init_l_eqns___closed__11();
lean_mark_persistent(l_eqns___closed__11);
l_eqns___closed__12 = _init_l_eqns___closed__12();
lean_mark_persistent(l_eqns___closed__12);
l_eqns___closed__13 = _init_l_eqns___closed__13();
lean_mark_persistent(l_eqns___closed__13);
l_eqns___closed__14 = _init_l_eqns___closed__14();
lean_mark_persistent(l_eqns___closed__14);
l_eqns___closed__15 = _init_l_eqns___closed__15();
lean_mark_persistent(l_eqns___closed__15);
l_eqns___closed__16 = _init_l_eqns___closed__16();
lean_mark_persistent(l_eqns___closed__16);
l_eqns___closed__17 = _init_l_eqns___closed__17();
lean_mark_persistent(l_eqns___closed__17);
l_eqns = _init_l_eqns();
lean_mark_persistent(l_eqns);
l_initFn____x40_Mathlib_Tactic_Eqns___hyg_36____lambda__2___closed__1 = _init_l_initFn____x40_Mathlib_Tactic_Eqns___hyg_36____lambda__2___closed__1();
lean_mark_persistent(l_initFn____x40_Mathlib_Tactic_Eqns___hyg_36____lambda__2___closed__1);
l_initFn____x40_Mathlib_Tactic_Eqns___hyg_36____closed__1 = _init_l_initFn____x40_Mathlib_Tactic_Eqns___hyg_36____closed__1();
lean_mark_persistent(l_initFn____x40_Mathlib_Tactic_Eqns___hyg_36____closed__1);
l_initFn____x40_Mathlib_Tactic_Eqns___hyg_36____closed__2 = _init_l_initFn____x40_Mathlib_Tactic_Eqns___hyg_36____closed__2();
lean_mark_persistent(l_initFn____x40_Mathlib_Tactic_Eqns___hyg_36____closed__2);
l_initFn____x40_Mathlib_Tactic_Eqns___hyg_36____closed__3 = _init_l_initFn____x40_Mathlib_Tactic_Eqns___hyg_36____closed__3();
lean_mark_persistent(l_initFn____x40_Mathlib_Tactic_Eqns___hyg_36____closed__3);
res = l_initFn____x40_Mathlib_Tactic_Eqns___hyg_36_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_eqnsAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_eqnsAttribute);
lean_dec_ref(res);
l_initFn____x40_Mathlib_Tactic_Eqns___hyg_259____lambda__1___closed__1 = _init_l_initFn____x40_Mathlib_Tactic_Eqns___hyg_259____lambda__1___closed__1();
lean_mark_persistent(l_initFn____x40_Mathlib_Tactic_Eqns___hyg_259____lambda__1___closed__1);
l_initFn____x40_Mathlib_Tactic_Eqns___hyg_259____closed__1 = _init_l_initFn____x40_Mathlib_Tactic_Eqns___hyg_259____closed__1();
lean_mark_persistent(l_initFn____x40_Mathlib_Tactic_Eqns___hyg_259____closed__1);
res = l_initFn____x40_Mathlib_Tactic_Eqns___hyg_259_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
