// Lean compiler output
// Module: Mathlib.Tactic.Clear!
// Imports: Init Lean
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
static lean_object* l_Mathlib_Tactic_clear_x21___closed__19;
static lean_object* l_Mathlib_Tactic_clear_x21___closed__23;
static lean_object* l_Mathlib_Tactic_clear_x21___closed__14;
static lean_object* l_Mathlib_Tactic_clear_x21___closed__17;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Mathlib_Tactic___aux__Mathlib__Tactic__Clear_x21______elabRules__Mathlib__Tactic__clear_x21__1___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getFVarIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Mathlib_Tactic_clear_x21___closed__12;
static lean_object* l_Mathlib_Tactic_clear_x21___closed__6;
static lean_object* l_Mathlib_Tactic_clear_x21___closed__11;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Mathlib_Tactic_clear_x21___closed__8;
static lean_object* l_Mathlib_Tactic_clear_x21___closed__20;
lean_object* l_Lean_Elab_Tactic_withMainContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Mathlib_Tactic_clear_x21___closed__16;
lean_object* l_Lean_Meta_collectForwardDeps(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Mathlib_Tactic_clear_x21___closed__1;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Mathlib_Tactic_clear_x21___closed__22;
static lean_object* l_Mathlib_Tactic_clear_x21___closed__13;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Mathlib_Tactic___aux__Mathlib__Tactic__Clear_x21______elabRules__Mathlib__Tactic__clear_x21__1___spec__1(size_t, size_t, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___spec__1___rarg(lean_object*);
static lean_object* l_Mathlib_Tactic_clear_x21___closed__2;
LEAN_EXPORT lean_object* l_Mathlib_Tactic_clear_x21;
static lean_object* l_Mathlib_Tactic_clear_x21___closed__7;
static lean_object* l_Mathlib_Tactic_clear_x21___closed__10;
static lean_object* l_Mathlib_Tactic_clear_x21___closed__3;
LEAN_EXPORT lean_object* l_Mathlib_Tactic___aux__Mathlib__Tactic__Clear_x21______elabRules__Mathlib__Tactic__clear_x21__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Mathlib_Tactic_clear_x21___closed__15;
lean_object* l_Lean_MVarId_tryClearMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Mathlib_Tactic_clear_x21___closed__9;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
static lean_object* l_Mathlib_Tactic_clear_x21___closed__21;
static lean_object* l_Mathlib_Tactic_clear_x21___closed__18;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_evalInduction___spec__2(size_t, size_t, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Mathlib_Tactic_clear_x21___closed__4;
static lean_object* l_Mathlib_Tactic_clear_x21___closed__5;
LEAN_EXPORT lean_object* l_Mathlib_Tactic___aux__Mathlib__Tactic__Clear_x21______elabRules__Mathlib__Tactic__clear_x21__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Mathlib_Tactic_clear_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Mathlib", 7);
return x_1;
}
}
static lean_object* _init_l_Mathlib_Tactic_clear_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Tactic", 6);
return x_1;
}
}
static lean_object* _init_l_Mathlib_Tactic_clear_x21___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("clear!", 6);
return x_1;
}
}
static lean_object* _init_l_Mathlib_Tactic_clear_x21___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Mathlib_Tactic_clear_x21___closed__1;
x_2 = l_Mathlib_Tactic_clear_x21___closed__2;
x_3 = l_Mathlib_Tactic_clear_x21___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Mathlib_Tactic_clear_x21___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("andthen", 7);
return x_1;
}
}
static lean_object* _init_l_Mathlib_Tactic_clear_x21___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Mathlib_Tactic_clear_x21___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Mathlib_Tactic_clear_x21___closed__7() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Mathlib_Tactic_clear_x21___closed__3;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Mathlib_Tactic_clear_x21___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("many", 4);
return x_1;
}
}
static lean_object* _init_l_Mathlib_Tactic_clear_x21___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Mathlib_Tactic_clear_x21___closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Mathlib_Tactic_clear_x21___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ppSpace", 7);
return x_1;
}
}
static lean_object* _init_l_Mathlib_Tactic_clear_x21___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Mathlib_Tactic_clear_x21___closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Mathlib_Tactic_clear_x21___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Mathlib_Tactic_clear_x21___closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Mathlib_Tactic_clear_x21___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("colGt", 5);
return x_1;
}
}
static lean_object* _init_l_Mathlib_Tactic_clear_x21___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Mathlib_Tactic_clear_x21___closed__13;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Mathlib_Tactic_clear_x21___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Mathlib_Tactic_clear_x21___closed__14;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Mathlib_Tactic_clear_x21___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Mathlib_Tactic_clear_x21___closed__6;
x_2 = l_Mathlib_Tactic_clear_x21___closed__12;
x_3 = l_Mathlib_Tactic_clear_x21___closed__15;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Mathlib_Tactic_clear_x21___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ident", 5);
return x_1;
}
}
static lean_object* _init_l_Mathlib_Tactic_clear_x21___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Mathlib_Tactic_clear_x21___closed__17;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Mathlib_Tactic_clear_x21___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Mathlib_Tactic_clear_x21___closed__18;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Mathlib_Tactic_clear_x21___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Mathlib_Tactic_clear_x21___closed__6;
x_2 = l_Mathlib_Tactic_clear_x21___closed__16;
x_3 = l_Mathlib_Tactic_clear_x21___closed__19;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Mathlib_Tactic_clear_x21___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Mathlib_Tactic_clear_x21___closed__9;
x_2 = l_Mathlib_Tactic_clear_x21___closed__20;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Mathlib_Tactic_clear_x21___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Mathlib_Tactic_clear_x21___closed__6;
x_2 = l_Mathlib_Tactic_clear_x21___closed__7;
x_3 = l_Mathlib_Tactic_clear_x21___closed__21;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Mathlib_Tactic_clear_x21___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Mathlib_Tactic_clear_x21___closed__4;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Mathlib_Tactic_clear_x21___closed__22;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Mathlib_Tactic_clear_x21() {
_start:
{
lean_object* x_1; 
x_1 = l_Mathlib_Tactic_clear_x21___closed__23;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Mathlib_Tactic___aux__Mathlib__Tactic__Clear_x21______elabRules__Mathlib__Tactic__clear_x21__1___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_Expr_fvar___override(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Mathlib_Tactic___aux__Mathlib__Tactic__Clear_x21______elabRules__Mathlib__Tactic__clear_x21__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_array_get_size(x_1);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_16 = 0;
x_17 = l_Array_mapMUnsafe_map___at_Mathlib_Tactic___aux__Mathlib__Tactic__Clear_x21______elabRules__Mathlib__Tactic__clear_x21__1___spec__1(x_15, x_16, x_1);
x_18 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = l_Lean_Meta_collectForwardDeps(x_17, x_18, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_array_get_size(x_20);
x_23 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_24 = l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_evalInduction___spec__2(x_23, x_16, x_20);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_25 = l_Lean_MVarId_tryClearMany(x_12, x_24, x_6, x_7, x_8, x_9, x_21);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_Elab_Tactic_replaceMainGoal(x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_27);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
return x_25;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_25);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_19);
if (x_35 == 0)
{
return x_19;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_19, 0);
x_37 = lean_ctor_get(x_19, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_19);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_11);
if (x_39 == 0)
{
return x_11;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_11, 0);
x_41 = lean_ctor_get(x_11, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_11);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Mathlib_Tactic___aux__Mathlib__Tactic__Clear_x21______elabRules__Mathlib__Tactic__clear_x21__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Mathlib_Tactic_clear_x21___closed__4;
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
x_16 = l_Lean_Syntax_getArgs(x_15);
lean_dec(x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_17 = l_Lean_Elab_Tactic_getFVarIds(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_closure((void*)(l_Mathlib_Tactic___aux__Mathlib__Tactic__Clear_x21______elabRules__Mathlib__Tactic__clear_x21__1___lambda__1), 10, 1);
lean_closure_set(x_20, 0, x_18);
x_21 = l_Lean_Elab_Tactic_withMainContext___rarg(x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 0);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_17);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Mathlib_Tactic___aux__Mathlib__Tactic__Clear_x21______elabRules__Mathlib__Tactic__clear_x21__1___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Mathlib_Tactic___aux__Mathlib__Tactic__Clear_x21______elabRules__Mathlib__Tactic__clear_x21__1___spec__1(x_4, x_5, x_3);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Mathlib_Tactic_Clear_x21(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Mathlib_Tactic_clear_x21___closed__1 = _init_l_Mathlib_Tactic_clear_x21___closed__1();
lean_mark_persistent(l_Mathlib_Tactic_clear_x21___closed__1);
l_Mathlib_Tactic_clear_x21___closed__2 = _init_l_Mathlib_Tactic_clear_x21___closed__2();
lean_mark_persistent(l_Mathlib_Tactic_clear_x21___closed__2);
l_Mathlib_Tactic_clear_x21___closed__3 = _init_l_Mathlib_Tactic_clear_x21___closed__3();
lean_mark_persistent(l_Mathlib_Tactic_clear_x21___closed__3);
l_Mathlib_Tactic_clear_x21___closed__4 = _init_l_Mathlib_Tactic_clear_x21___closed__4();
lean_mark_persistent(l_Mathlib_Tactic_clear_x21___closed__4);
l_Mathlib_Tactic_clear_x21___closed__5 = _init_l_Mathlib_Tactic_clear_x21___closed__5();
lean_mark_persistent(l_Mathlib_Tactic_clear_x21___closed__5);
l_Mathlib_Tactic_clear_x21___closed__6 = _init_l_Mathlib_Tactic_clear_x21___closed__6();
lean_mark_persistent(l_Mathlib_Tactic_clear_x21___closed__6);
l_Mathlib_Tactic_clear_x21___closed__7 = _init_l_Mathlib_Tactic_clear_x21___closed__7();
lean_mark_persistent(l_Mathlib_Tactic_clear_x21___closed__7);
l_Mathlib_Tactic_clear_x21___closed__8 = _init_l_Mathlib_Tactic_clear_x21___closed__8();
lean_mark_persistent(l_Mathlib_Tactic_clear_x21___closed__8);
l_Mathlib_Tactic_clear_x21___closed__9 = _init_l_Mathlib_Tactic_clear_x21___closed__9();
lean_mark_persistent(l_Mathlib_Tactic_clear_x21___closed__9);
l_Mathlib_Tactic_clear_x21___closed__10 = _init_l_Mathlib_Tactic_clear_x21___closed__10();
lean_mark_persistent(l_Mathlib_Tactic_clear_x21___closed__10);
l_Mathlib_Tactic_clear_x21___closed__11 = _init_l_Mathlib_Tactic_clear_x21___closed__11();
lean_mark_persistent(l_Mathlib_Tactic_clear_x21___closed__11);
l_Mathlib_Tactic_clear_x21___closed__12 = _init_l_Mathlib_Tactic_clear_x21___closed__12();
lean_mark_persistent(l_Mathlib_Tactic_clear_x21___closed__12);
l_Mathlib_Tactic_clear_x21___closed__13 = _init_l_Mathlib_Tactic_clear_x21___closed__13();
lean_mark_persistent(l_Mathlib_Tactic_clear_x21___closed__13);
l_Mathlib_Tactic_clear_x21___closed__14 = _init_l_Mathlib_Tactic_clear_x21___closed__14();
lean_mark_persistent(l_Mathlib_Tactic_clear_x21___closed__14);
l_Mathlib_Tactic_clear_x21___closed__15 = _init_l_Mathlib_Tactic_clear_x21___closed__15();
lean_mark_persistent(l_Mathlib_Tactic_clear_x21___closed__15);
l_Mathlib_Tactic_clear_x21___closed__16 = _init_l_Mathlib_Tactic_clear_x21___closed__16();
lean_mark_persistent(l_Mathlib_Tactic_clear_x21___closed__16);
l_Mathlib_Tactic_clear_x21___closed__17 = _init_l_Mathlib_Tactic_clear_x21___closed__17();
lean_mark_persistent(l_Mathlib_Tactic_clear_x21___closed__17);
l_Mathlib_Tactic_clear_x21___closed__18 = _init_l_Mathlib_Tactic_clear_x21___closed__18();
lean_mark_persistent(l_Mathlib_Tactic_clear_x21___closed__18);
l_Mathlib_Tactic_clear_x21___closed__19 = _init_l_Mathlib_Tactic_clear_x21___closed__19();
lean_mark_persistent(l_Mathlib_Tactic_clear_x21___closed__19);
l_Mathlib_Tactic_clear_x21___closed__20 = _init_l_Mathlib_Tactic_clear_x21___closed__20();
lean_mark_persistent(l_Mathlib_Tactic_clear_x21___closed__20);
l_Mathlib_Tactic_clear_x21___closed__21 = _init_l_Mathlib_Tactic_clear_x21___closed__21();
lean_mark_persistent(l_Mathlib_Tactic_clear_x21___closed__21);
l_Mathlib_Tactic_clear_x21___closed__22 = _init_l_Mathlib_Tactic_clear_x21___closed__22();
lean_mark_persistent(l_Mathlib_Tactic_clear_x21___closed__22);
l_Mathlib_Tactic_clear_x21___closed__23 = _init_l_Mathlib_Tactic_clear_x21___closed__23();
lean_mark_persistent(l_Mathlib_Tactic_clear_x21___closed__23);
l_Mathlib_Tactic_clear_x21 = _init_l_Mathlib_Tactic_clear_x21();
lean_mark_persistent(l_Mathlib_Tactic_clear_x21);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
