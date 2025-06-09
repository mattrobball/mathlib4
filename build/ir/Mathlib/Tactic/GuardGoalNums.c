// Lean compiler output
// Module: Mathlib.Tactic.GuardGoalNums
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
LEAN_EXPORT lean_object* l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_guardGoalNums___closed__11;
static lean_object* l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___lambda__1___closed__1;
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic_throwExs___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withoutRecover___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_guardGoalNums___closed__8;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_restore(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__7;
lean_object* l_Lean_Elab_Tactic_getGoals___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_guardGoalNums___closed__7;
static lean_object* l_guardGoalNums___closed__10;
static lean_object* l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___lambda__1___closed__2;
static lean_object* l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__1;
static lean_object* l_guardGoalNums___closed__5;
LEAN_EXPORT lean_object* l_guardGoalNums;
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__6;
LEAN_EXPORT lean_object* l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__4;
static lean_object* l_guardGoalNums___closed__2;
static lean_object* l_guardGoalNums___closed__4;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___spec__1___rarg(lean_object*);
lean_object* l_Lean_Elab_Tactic_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_guardGoalNums___closed__1;
static lean_object* l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__2;
lean_object* l_Lean_TSyntax_getNat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__5;
static lean_object* l_guardGoalNums___closed__3;
lean_object* l_ReaderT_pure___at_Lean_Elab_Tactic_saveTacticInfoForToken___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_guardGoalNums___closed__9;
static lean_object* l_guardGoalNums___closed__6;
LEAN_EXPORT lean_object* l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__3;
lean_object* l_Nat_repr(lean_object*);
static lean_object* l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__8;
static lean_object* _init_l_guardGoalNums___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("guardGoalNums", 13);
return x_1;
}
}
static lean_object* _init_l_guardGoalNums___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_guardGoalNums___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_guardGoalNums___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("andthen", 7);
return x_1;
}
}
static lean_object* _init_l_guardGoalNums___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_guardGoalNums___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_guardGoalNums___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("guard_goal_nums ", 16);
return x_1;
}
}
static lean_object* _init_l_guardGoalNums___closed__6() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_guardGoalNums___closed__5;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_guardGoalNums___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("num", 3);
return x_1;
}
}
static lean_object* _init_l_guardGoalNums___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_guardGoalNums___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_guardGoalNums___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_guardGoalNums___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_guardGoalNums___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_guardGoalNums___closed__4;
x_2 = l_guardGoalNums___closed__6;
x_3 = l_guardGoalNums___closed__9;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_guardGoalNums___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_guardGoalNums___closed__2;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_guardGoalNums___closed__10;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_guardGoalNums() {
_start:
{
lean_object* x_1; 
x_1 = l_guardGoalNums___closed__11;
return x_1;
}
}
static lean_object* _init_l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("failed", 6);
return x_1;
}
}
static lean_object* _init_l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___lambda__1___closed__2;
x_11 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic_throwExs___spec__2(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("expected ", 9);
return x_1;
}
}
static lean_object* _init_l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" goals but found ", 17);
return x_1;
}
}
static lean_object* _init_l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___lambda__1___boxed), 9, 0);
return x_1;
}
}
static lean_object* _init_l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Elab_Tactic_saveTacticInfoForToken___spec__1___rarg___boxed), 10, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_guardGoalNums___closed__2;
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_45; lean_object* x_46; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
x_16 = l_Lean_Elab_Tactic_getGoals___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_List_lengthTRAux___rarg(x_17, x_19);
lean_dec(x_17);
x_21 = l_Lean_TSyntax_getNat(x_15);
lean_dec(x_15);
x_45 = lean_nat_dec_eq(x_20, x_21);
x_46 = l_Lean_Elab_Tactic_saveState___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
if (x_45 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__7;
x_22 = x_49;
x_23 = x_47;
x_24 = x_48;
goto block_44;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_46, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_dec(x_46);
x_52 = l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__8;
x_22 = x_52;
x_23 = x_50;
x_24 = x_51;
goto block_44;
}
block_44:
{
lean_object* x_25; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_25 = l_Lean_Elab_Tactic_withoutRecover___rarg(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_25;
}
else
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_28 = l_Lean_Elab_Tactic_SavedState_restore(x_23, x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_26);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Nat_repr(x_21);
x_31 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__2;
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__4;
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Nat_repr(x_20);
x_38 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_39);
x_41 = l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__6;
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic_throwExs___spec__2(x_42, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_43;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Mathlib_Tactic_GuardGoalNums(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_guardGoalNums___closed__1 = _init_l_guardGoalNums___closed__1();
lean_mark_persistent(l_guardGoalNums___closed__1);
l_guardGoalNums___closed__2 = _init_l_guardGoalNums___closed__2();
lean_mark_persistent(l_guardGoalNums___closed__2);
l_guardGoalNums___closed__3 = _init_l_guardGoalNums___closed__3();
lean_mark_persistent(l_guardGoalNums___closed__3);
l_guardGoalNums___closed__4 = _init_l_guardGoalNums___closed__4();
lean_mark_persistent(l_guardGoalNums___closed__4);
l_guardGoalNums___closed__5 = _init_l_guardGoalNums___closed__5();
lean_mark_persistent(l_guardGoalNums___closed__5);
l_guardGoalNums___closed__6 = _init_l_guardGoalNums___closed__6();
lean_mark_persistent(l_guardGoalNums___closed__6);
l_guardGoalNums___closed__7 = _init_l_guardGoalNums___closed__7();
lean_mark_persistent(l_guardGoalNums___closed__7);
l_guardGoalNums___closed__8 = _init_l_guardGoalNums___closed__8();
lean_mark_persistent(l_guardGoalNums___closed__8);
l_guardGoalNums___closed__9 = _init_l_guardGoalNums___closed__9();
lean_mark_persistent(l_guardGoalNums___closed__9);
l_guardGoalNums___closed__10 = _init_l_guardGoalNums___closed__10();
lean_mark_persistent(l_guardGoalNums___closed__10);
l_guardGoalNums___closed__11 = _init_l_guardGoalNums___closed__11();
lean_mark_persistent(l_guardGoalNums___closed__11);
l_guardGoalNums = _init_l_guardGoalNums();
lean_mark_persistent(l_guardGoalNums);
l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___lambda__1___closed__1 = _init_l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___lambda__1___closed__1();
lean_mark_persistent(l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___lambda__1___closed__1);
l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___lambda__1___closed__2 = _init_l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___lambda__1___closed__2();
lean_mark_persistent(l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___lambda__1___closed__2);
l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__1 = _init_l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__1();
lean_mark_persistent(l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__1);
l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__2 = _init_l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__2();
lean_mark_persistent(l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__2);
l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__3 = _init_l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__3();
lean_mark_persistent(l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__3);
l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__4 = _init_l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__4();
lean_mark_persistent(l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__4);
l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__5 = _init_l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__5();
lean_mark_persistent(l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__5);
l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__6 = _init_l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__6();
lean_mark_persistent(l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__6);
l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__7 = _init_l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__7();
lean_mark_persistent(l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__7);
l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__8 = _init_l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__8();
lean_mark_persistent(l___aux__Mathlib__Tactic__GuardGoalNums______elabRules__guardGoalNums__1___closed__8);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
