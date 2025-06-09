// Lean compiler output
// Module: Mathlib.Util.AssertExists
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
lean_object* l_Lean_Elab_resolveGlobalConstWithInfos___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_commandAssert__not__exists__;
static lean_object* l_commandAssert__exists_____closed__8;
static lean_object* l_commandAssert__exists_____closed__5;
static lean_object* l_commandAssert__exists_____closed__9;
static lean_object* l___aux__Mathlib__Util__AssertExists______elabRules__commandAssert__not__exists____1___lambda__1___closed__2;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Widget_elabWidgetCmd___spec__1___rarg(lean_object*);
static lean_object* l_commandAssert__exists_____closed__7;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
static lean_object* l_commandAssert__not__exists_____closed__1;
static lean_object* l_commandAssert__not__exists_____closed__6;
LEAN_EXPORT lean_object* l_commandAssert__exists__;
LEAN_EXPORT lean_object* l___aux__Mathlib__Util__AssertExists______elabRules__commandAssert__not__exists____1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_commandAssert__exists_____closed__6;
lean_object* l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at_Lean_Elab_Command_elabAddDeclDoc___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Mathlib__Util__AssertExists______elabRules__commandAssert__not__exists____1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l___aux__Mathlib__Util__AssertExists______elabRules__commandAssert__not__exists____1___lambda__1___closed__1;
static lean_object* l_commandAssert__exists_____closed__3;
static lean_object* l_commandAssert__not__exists_____closed__3;
static lean_object* l_commandAssert__not__exists_____closed__5;
static lean_object* l___aux__Mathlib__Util__AssertExists______elabRules__commandAssert__not__exists____1___lambda__1___closed__4;
static lean_object* l_commandAssert__exists_____closed__2;
static lean_object* l_commandAssert__exists_____closed__1;
LEAN_EXPORT lean_object* l___aux__Mathlib__Util__AssertExists______elabRules__commandAssert__not__exists____1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_commandAssert__exists_____closed__4;
static lean_object* l_commandAssert__exists_____closed__11;
LEAN_EXPORT lean_object* l___aux__Mathlib__Util__AssertExists______elabRules__commandAssert__exists____1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Mathlib__Util__AssertExists______elabRules__commandAssert__not__exists____1___lambda__1___closed__3;
static lean_object* l_commandAssert__not__exists_____closed__4;
static lean_object* l_commandAssert__exists_____closed__10;
static lean_object* l_commandAssert__not__exists_____closed__2;
static lean_object* _init_l_commandAssert__exists_____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("commandAssert_exists_", 21);
return x_1;
}
}
static lean_object* _init_l_commandAssert__exists_____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_commandAssert__exists_____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_commandAssert__exists_____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("andthen", 7);
return x_1;
}
}
static lean_object* _init_l_commandAssert__exists_____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_commandAssert__exists_____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_commandAssert__exists_____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("assert_exists ", 14);
return x_1;
}
}
static lean_object* _init_l_commandAssert__exists_____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_commandAssert__exists_____closed__5;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_commandAssert__exists_____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ident", 5);
return x_1;
}
}
static lean_object* _init_l_commandAssert__exists_____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_commandAssert__exists_____closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_commandAssert__exists_____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_commandAssert__exists_____closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_commandAssert__exists_____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_commandAssert__exists_____closed__4;
x_2 = l_commandAssert__exists_____closed__6;
x_3 = l_commandAssert__exists_____closed__9;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_commandAssert__exists_____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_commandAssert__exists_____closed__2;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_commandAssert__exists_____closed__10;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_commandAssert__exists__() {
_start:
{
lean_object* x_1; 
x_1 = l_commandAssert__exists_____closed__11;
return x_1;
}
}
LEAN_EXPORT lean_object* l___aux__Mathlib__Util__AssertExists______elabRules__commandAssert__exists____1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_commandAssert__exists_____closed__2;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Widget_elabWidgetCmd___spec__1___rarg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at_Lean_Elab_Command_elabAddDeclDoc___spec__1(x_9, x_10, x_2, x_3, x_4);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
static lean_object* _init_l_commandAssert__not__exists_____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("commandAssert_not_exists_", 25);
return x_1;
}
}
static lean_object* _init_l_commandAssert__not__exists_____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_commandAssert__not__exists_____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_commandAssert__not__exists_____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("assert_not_exists ", 18);
return x_1;
}
}
static lean_object* _init_l_commandAssert__not__exists_____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_commandAssert__not__exists_____closed__3;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_commandAssert__not__exists_____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_commandAssert__exists_____closed__4;
x_2 = l_commandAssert__not__exists_____closed__4;
x_3 = l_commandAssert__exists_____closed__9;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_commandAssert__not__exists_____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_commandAssert__not__exists_____closed__2;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_commandAssert__not__exists_____closed__5;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_commandAssert__not__exists__() {
_start:
{
lean_object* x_1; 
x_1 = l_commandAssert__not__exists_____closed__6;
return x_1;
}
}
static lean_object* _init_l___aux__Mathlib__Util__AssertExists______elabRules__commandAssert__not__exists____1___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Declaration ", 12);
return x_1;
}
}
static lean_object* _init_l___aux__Mathlib__Util__AssertExists______elabRules__commandAssert__not__exists____1___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Mathlib__Util__AssertExists______elabRules__commandAssert__not__exists____1___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Mathlib__Util__AssertExists______elabRules__commandAssert__not__exists____1___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" is not allowed to exist in this file", 37);
return x_1;
}
}
static lean_object* _init_l___aux__Mathlib__Util__AssertExists______elabRules__commandAssert__not__exists____1___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Mathlib__Util__AssertExists______elabRules__commandAssert__not__exists____1___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___aux__Mathlib__Util__AssertExists______elabRules__commandAssert__not__exists____1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_8 = l_Lean_MessageData_ofSyntax(x_1);
x_9 = l___aux__Mathlib__Util__AssertExists______elabRules__commandAssert__not__exists____1___lambda__1___closed__2;
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l___aux__Mathlib__Util__AssertExists______elabRules__commandAssert__not__exists____1___lambda__1___closed__4;
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_5);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___aux__Mathlib__Util__AssertExists______elabRules__commandAssert__not__exists____1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_commandAssert__not__exists_____closed__2;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Widget_elabWidgetCmd___spec__1___rarg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
x_10 = lean_box(0);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_9);
x_11 = l_Lean_Elab_resolveGlobalConstWithInfos___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__2(x_9, x_10, x_2, x_3, x_4);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___aux__Mathlib__Util__AssertExists______elabRules__commandAssert__not__exists____1___lambda__1(x_9, x_12, x_2, x_3, x_13);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_12);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_11, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set_tag(x_11, 0);
lean_ctor_set(x_11, 0, x_17);
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Mathlib__Util__AssertExists______elabRules__commandAssert__not__exists____1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___aux__Mathlib__Util__AssertExists______elabRules__commandAssert__not__exists____1___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Mathlib_Util_AssertExists(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_commandAssert__exists_____closed__1 = _init_l_commandAssert__exists_____closed__1();
lean_mark_persistent(l_commandAssert__exists_____closed__1);
l_commandAssert__exists_____closed__2 = _init_l_commandAssert__exists_____closed__2();
lean_mark_persistent(l_commandAssert__exists_____closed__2);
l_commandAssert__exists_____closed__3 = _init_l_commandAssert__exists_____closed__3();
lean_mark_persistent(l_commandAssert__exists_____closed__3);
l_commandAssert__exists_____closed__4 = _init_l_commandAssert__exists_____closed__4();
lean_mark_persistent(l_commandAssert__exists_____closed__4);
l_commandAssert__exists_____closed__5 = _init_l_commandAssert__exists_____closed__5();
lean_mark_persistent(l_commandAssert__exists_____closed__5);
l_commandAssert__exists_____closed__6 = _init_l_commandAssert__exists_____closed__6();
lean_mark_persistent(l_commandAssert__exists_____closed__6);
l_commandAssert__exists_____closed__7 = _init_l_commandAssert__exists_____closed__7();
lean_mark_persistent(l_commandAssert__exists_____closed__7);
l_commandAssert__exists_____closed__8 = _init_l_commandAssert__exists_____closed__8();
lean_mark_persistent(l_commandAssert__exists_____closed__8);
l_commandAssert__exists_____closed__9 = _init_l_commandAssert__exists_____closed__9();
lean_mark_persistent(l_commandAssert__exists_____closed__9);
l_commandAssert__exists_____closed__10 = _init_l_commandAssert__exists_____closed__10();
lean_mark_persistent(l_commandAssert__exists_____closed__10);
l_commandAssert__exists_____closed__11 = _init_l_commandAssert__exists_____closed__11();
lean_mark_persistent(l_commandAssert__exists_____closed__11);
l_commandAssert__exists__ = _init_l_commandAssert__exists__();
lean_mark_persistent(l_commandAssert__exists__);
l_commandAssert__not__exists_____closed__1 = _init_l_commandAssert__not__exists_____closed__1();
lean_mark_persistent(l_commandAssert__not__exists_____closed__1);
l_commandAssert__not__exists_____closed__2 = _init_l_commandAssert__not__exists_____closed__2();
lean_mark_persistent(l_commandAssert__not__exists_____closed__2);
l_commandAssert__not__exists_____closed__3 = _init_l_commandAssert__not__exists_____closed__3();
lean_mark_persistent(l_commandAssert__not__exists_____closed__3);
l_commandAssert__not__exists_____closed__4 = _init_l_commandAssert__not__exists_____closed__4();
lean_mark_persistent(l_commandAssert__not__exists_____closed__4);
l_commandAssert__not__exists_____closed__5 = _init_l_commandAssert__not__exists_____closed__5();
lean_mark_persistent(l_commandAssert__not__exists_____closed__5);
l_commandAssert__not__exists_____closed__6 = _init_l_commandAssert__not__exists_____closed__6();
lean_mark_persistent(l_commandAssert__not__exists_____closed__6);
l_commandAssert__not__exists__ = _init_l_commandAssert__not__exists__();
lean_mark_persistent(l_commandAssert__not__exists__);
l___aux__Mathlib__Util__AssertExists______elabRules__commandAssert__not__exists____1___lambda__1___closed__1 = _init_l___aux__Mathlib__Util__AssertExists______elabRules__commandAssert__not__exists____1___lambda__1___closed__1();
lean_mark_persistent(l___aux__Mathlib__Util__AssertExists______elabRules__commandAssert__not__exists____1___lambda__1___closed__1);
l___aux__Mathlib__Util__AssertExists______elabRules__commandAssert__not__exists____1___lambda__1___closed__2 = _init_l___aux__Mathlib__Util__AssertExists______elabRules__commandAssert__not__exists____1___lambda__1___closed__2();
lean_mark_persistent(l___aux__Mathlib__Util__AssertExists______elabRules__commandAssert__not__exists____1___lambda__1___closed__2);
l___aux__Mathlib__Util__AssertExists______elabRules__commandAssert__not__exists____1___lambda__1___closed__3 = _init_l___aux__Mathlib__Util__AssertExists______elabRules__commandAssert__not__exists____1___lambda__1___closed__3();
lean_mark_persistent(l___aux__Mathlib__Util__AssertExists______elabRules__commandAssert__not__exists____1___lambda__1___closed__3);
l___aux__Mathlib__Util__AssertExists______elabRules__commandAssert__not__exists____1___lambda__1___closed__4 = _init_l___aux__Mathlib__Util__AssertExists______elabRules__commandAssert__not__exists____1___lambda__1___closed__4();
lean_mark_persistent(l___aux__Mathlib__Util__AssertExists______elabRules__commandAssert__not__exists____1___lambda__1___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
