// Lean compiler output
// Module: Mathlib.Util.WithWeakNamespace
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
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Widget_elabWidgetCmd___spec__1___rarg(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Environment_registerNamespace(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_commandWith__weak__namespace_______closed__9;
static lean_object* l_Lean_Elab_Command_commandWith__weak__namespace_______closed__16;
static lean_object* l_Lean_Elab_Command_commandWith__weak__namespace_______closed__10;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_commandWith__weak__namespace_______closed__7;
static lean_object* l_Lean_Elab_Command_commandWith__weak__namespace_______closed__2;
static lean_object* l_Lean_Elab_Command_commandWith__weak__namespace_______closed__4;
static lean_object* l_Lean_Elab_Command_commandWith__weak__namespace_______closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Command___aux__Mathlib__Util__WithWeakNamespace______elabRules__Lean__Elab__Command__commandWith__weak__namespace______1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_commandWith__weak__namespace_______closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withWeakNamespace___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getScope___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_commandWith__weak__namespace_______closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withWeakNamespace(lean_object*);
static lean_object* l_Lean_Elab_Command_commandWith__weak__namespace_______closed__18;
static lean_object* l_Lean_Elab_Command_commandWith__weak__namespace_______closed__17;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_resolveNamespace___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withWeakNamespace___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_commandWith__weak__namespace_______closed__1;
static lean_object* l_Lean_Elab_Command_commandWith__weak__namespace_______closed__11;
static lean_object* l_Lean_Elab_Command_resolveNamespace___closed__1;
static lean_object* l_Lean_Elab_Command_commandWith__weak__namespace_______closed__14;
static lean_object* l_Lean_Elab_Command_commandWith__weak__namespace_______closed__13;
static lean_object* l_Lean_Elab_Command_commandWith__weak__namespace_______closed__12;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_commandWith__weak__namespace____;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_resolveNamespace(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_commandWith__weak__namespace_______closed__15;
static lean_object* l_Lean_Elab_Command_commandWith__weak__namespace_______closed__3;
static lean_object* _init_l_Lean_Elab_Command_resolveNamespace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_root_", 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_resolveNamespace(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_inc(x_1);
return x_1;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Elab_Command_resolveNamespace___closed__1;
x_6 = lean_string_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Elab_Command_resolveNamespace(x_1, x_3);
x_8 = l_Lean_Name_str___override(x_7, x_4);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_4);
x_9 = lean_box(0);
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec(x_2);
x_11 = l_Lean_Elab_Command_resolveNamespace(x_1, x_3);
x_12 = l_Lean_Name_str___override(x_11, x_10);
return x_12;
}
}
default: 
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec(x_2);
x_15 = l_Lean_Elab_Command_resolveNamespace(x_1, x_13);
x_16 = l_Lean_Name_num___override(x_15, x_14);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_resolveNamespace___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_resolveNamespace(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withWeakNamespace___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 2);
lean_dec(x_4);
lean_ctor_set(x_2, 2, x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 3);
x_8 = lean_ctor_get(x_2, 4);
x_9 = lean_ctor_get(x_2, 5);
x_10 = lean_ctor_get(x_2, 6);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*7);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_6);
lean_ctor_set(x_12, 2, x_1);
lean_ctor_set(x_12, 3, x_7);
lean_ctor_set(x_12, 4, x_8);
lean_ctor_set(x_12, 5, x_9);
lean_ctor_set(x_12, 6, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*7, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withWeakNamespace___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_6 = l_Lean_Elab_Command_getScope___rarg(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 2);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Elab_Command_resolveNamespace(x_9, x_1);
x_11 = lean_st_ref_take(x_4, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_10);
x_16 = l_Lean_Environment_registerNamespace(x_15, x_10);
lean_ctor_set(x_12, 0, x_16);
x_17 = lean_st_ref_set(x_4, x_12, x_13);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_Command_withWeakNamespace___rarg___lambda__1), 2, 1);
lean_closure_set(x_19, 0, x_10);
x_20 = l_Lean_Elab_Command_modifyScope(x_19, x_3, x_4, x_18);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_Command_withWeakNamespace___rarg___lambda__1), 2, 1);
lean_closure_set(x_22, 0, x_9);
lean_inc(x_4);
lean_inc(x_3);
x_23 = lean_apply_3(x_2, x_3, x_4, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Elab_Command_modifyScope(x_22, x_3, x_4, x_25);
lean_dec(x_4);
lean_dec(x_3);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_24);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_23, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_dec(x_23);
x_33 = l_Lean_Elab_Command_modifyScope(x_22, x_3, x_4, x_32);
lean_dec(x_4);
lean_dec(x_3);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set_tag(x_33, 1);
lean_ctor_set(x_33, 0, x_31);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_38 = lean_ctor_get(x_12, 0);
x_39 = lean_ctor_get(x_12, 1);
x_40 = lean_ctor_get(x_12, 2);
x_41 = lean_ctor_get(x_12, 3);
x_42 = lean_ctor_get(x_12, 4);
x_43 = lean_ctor_get(x_12, 5);
x_44 = lean_ctor_get(x_12, 6);
x_45 = lean_ctor_get(x_12, 7);
x_46 = lean_ctor_get(x_12, 8);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_12);
lean_inc(x_10);
x_47 = l_Lean_Environment_registerNamespace(x_38, x_10);
x_48 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_39);
lean_ctor_set(x_48, 2, x_40);
lean_ctor_set(x_48, 3, x_41);
lean_ctor_set(x_48, 4, x_42);
lean_ctor_set(x_48, 5, x_43);
lean_ctor_set(x_48, 6, x_44);
lean_ctor_set(x_48, 7, x_45);
lean_ctor_set(x_48, 8, x_46);
x_49 = lean_st_ref_set(x_4, x_48, x_13);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_alloc_closure((void*)(l_Lean_Elab_Command_withWeakNamespace___rarg___lambda__1), 2, 1);
lean_closure_set(x_51, 0, x_10);
x_52 = l_Lean_Elab_Command_modifyScope(x_51, x_3, x_4, x_50);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_alloc_closure((void*)(l_Lean_Elab_Command_withWeakNamespace___rarg___lambda__1), 2, 1);
lean_closure_set(x_54, 0, x_9);
lean_inc(x_4);
lean_inc(x_3);
x_55 = lean_apply_3(x_2, x_3, x_4, x_53);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_Lean_Elab_Command_modifyScope(x_54, x_3, x_4, x_57);
lean_dec(x_4);
lean_dec(x_3);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_56);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_55, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_55, 1);
lean_inc(x_63);
lean_dec(x_55);
x_64 = l_Lean_Elab_Command_modifyScope(x_54, x_3, x_4, x_63);
lean_dec(x_4);
lean_dec(x_3);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_66 = x_64;
} else {
 lean_dec_ref(x_64);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
 lean_ctor_set_tag(x_67, 1);
}
lean_ctor_set(x_67, 0, x_62);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withWeakNamespace(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_withWeakNamespace___rarg), 5, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_commandWith__weak__namespace_______closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_commandWith__weak__namespace_______closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Elab", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_commandWith__weak__namespace_______closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Command", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_commandWith__weak__namespace_______closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("commandWith_weak_namespace__", 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_commandWith__weak__namespace_______closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_commandWith__weak__namespace_______closed__1;
x_2 = l_Lean_Elab_Command_commandWith__weak__namespace_______closed__2;
x_3 = l_Lean_Elab_Command_commandWith__weak__namespace_______closed__3;
x_4 = l_Lean_Elab_Command_commandWith__weak__namespace_______closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_commandWith__weak__namespace_______closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("andthen", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_commandWith__weak__namespace_______closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_commandWith__weak__namespace_______closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_commandWith__weak__namespace_______closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("with_weak_namespace ", 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_commandWith__weak__namespace_______closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_commandWith__weak__namespace_______closed__8;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_commandWith__weak__namespace_______closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ident", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_commandWith__weak__namespace_______closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_commandWith__weak__namespace_______closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_commandWith__weak__namespace_______closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_commandWith__weak__namespace_______closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_commandWith__weak__namespace_______closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_commandWith__weak__namespace_______closed__7;
x_2 = l_Lean_Elab_Command_commandWith__weak__namespace_______closed__9;
x_3 = l_Lean_Elab_Command_commandWith__weak__namespace_______closed__12;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_commandWith__weak__namespace_______closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("command", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_commandWith__weak__namespace_______closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_commandWith__weak__namespace_______closed__14;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_commandWith__weak__namespace_______closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_commandWith__weak__namespace_______closed__15;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_commandWith__weak__namespace_______closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_commandWith__weak__namespace_______closed__7;
x_2 = l_Lean_Elab_Command_commandWith__weak__namespace_______closed__13;
x_3 = l_Lean_Elab_Command_commandWith__weak__namespace_______closed__16;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_commandWith__weak__namespace_______closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_commandWith__weak__namespace_______closed__5;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_Elab_Command_commandWith__weak__namespace_______closed__17;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_commandWith__weak__namespace____() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_commandWith__weak__namespace_______closed__18;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command___aux__Mathlib__Util__WithWeakNamespace______elabRules__Lean__Elab__Command__commandWith__weak__namespace______1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Command_commandWith__weak__namespace_______closed__5;
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
x_12 = l_Lean_Syntax_getId(x_9);
lean_dec(x_9);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_13, 0, x_11);
x_14 = l_Lean_Elab_Command_withWeakNamespace___rarg(x_12, x_13, x_2, x_3, x_4);
return x_14;
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Mathlib_Util_WithWeakNamespace(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_resolveNamespace___closed__1 = _init_l_Lean_Elab_Command_resolveNamespace___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_resolveNamespace___closed__1);
l_Lean_Elab_Command_commandWith__weak__namespace_______closed__1 = _init_l_Lean_Elab_Command_commandWith__weak__namespace_______closed__1();
lean_mark_persistent(l_Lean_Elab_Command_commandWith__weak__namespace_______closed__1);
l_Lean_Elab_Command_commandWith__weak__namespace_______closed__2 = _init_l_Lean_Elab_Command_commandWith__weak__namespace_______closed__2();
lean_mark_persistent(l_Lean_Elab_Command_commandWith__weak__namespace_______closed__2);
l_Lean_Elab_Command_commandWith__weak__namespace_______closed__3 = _init_l_Lean_Elab_Command_commandWith__weak__namespace_______closed__3();
lean_mark_persistent(l_Lean_Elab_Command_commandWith__weak__namespace_______closed__3);
l_Lean_Elab_Command_commandWith__weak__namespace_______closed__4 = _init_l_Lean_Elab_Command_commandWith__weak__namespace_______closed__4();
lean_mark_persistent(l_Lean_Elab_Command_commandWith__weak__namespace_______closed__4);
l_Lean_Elab_Command_commandWith__weak__namespace_______closed__5 = _init_l_Lean_Elab_Command_commandWith__weak__namespace_______closed__5();
lean_mark_persistent(l_Lean_Elab_Command_commandWith__weak__namespace_______closed__5);
l_Lean_Elab_Command_commandWith__weak__namespace_______closed__6 = _init_l_Lean_Elab_Command_commandWith__weak__namespace_______closed__6();
lean_mark_persistent(l_Lean_Elab_Command_commandWith__weak__namespace_______closed__6);
l_Lean_Elab_Command_commandWith__weak__namespace_______closed__7 = _init_l_Lean_Elab_Command_commandWith__weak__namespace_______closed__7();
lean_mark_persistent(l_Lean_Elab_Command_commandWith__weak__namespace_______closed__7);
l_Lean_Elab_Command_commandWith__weak__namespace_______closed__8 = _init_l_Lean_Elab_Command_commandWith__weak__namespace_______closed__8();
lean_mark_persistent(l_Lean_Elab_Command_commandWith__weak__namespace_______closed__8);
l_Lean_Elab_Command_commandWith__weak__namespace_______closed__9 = _init_l_Lean_Elab_Command_commandWith__weak__namespace_______closed__9();
lean_mark_persistent(l_Lean_Elab_Command_commandWith__weak__namespace_______closed__9);
l_Lean_Elab_Command_commandWith__weak__namespace_______closed__10 = _init_l_Lean_Elab_Command_commandWith__weak__namespace_______closed__10();
lean_mark_persistent(l_Lean_Elab_Command_commandWith__weak__namespace_______closed__10);
l_Lean_Elab_Command_commandWith__weak__namespace_______closed__11 = _init_l_Lean_Elab_Command_commandWith__weak__namespace_______closed__11();
lean_mark_persistent(l_Lean_Elab_Command_commandWith__weak__namespace_______closed__11);
l_Lean_Elab_Command_commandWith__weak__namespace_______closed__12 = _init_l_Lean_Elab_Command_commandWith__weak__namespace_______closed__12();
lean_mark_persistent(l_Lean_Elab_Command_commandWith__weak__namespace_______closed__12);
l_Lean_Elab_Command_commandWith__weak__namespace_______closed__13 = _init_l_Lean_Elab_Command_commandWith__weak__namespace_______closed__13();
lean_mark_persistent(l_Lean_Elab_Command_commandWith__weak__namespace_______closed__13);
l_Lean_Elab_Command_commandWith__weak__namespace_______closed__14 = _init_l_Lean_Elab_Command_commandWith__weak__namespace_______closed__14();
lean_mark_persistent(l_Lean_Elab_Command_commandWith__weak__namespace_______closed__14);
l_Lean_Elab_Command_commandWith__weak__namespace_______closed__15 = _init_l_Lean_Elab_Command_commandWith__weak__namespace_______closed__15();
lean_mark_persistent(l_Lean_Elab_Command_commandWith__weak__namespace_______closed__15);
l_Lean_Elab_Command_commandWith__weak__namespace_______closed__16 = _init_l_Lean_Elab_Command_commandWith__weak__namespace_______closed__16();
lean_mark_persistent(l_Lean_Elab_Command_commandWith__weak__namespace_______closed__16);
l_Lean_Elab_Command_commandWith__weak__namespace_______closed__17 = _init_l_Lean_Elab_Command_commandWith__weak__namespace_______closed__17();
lean_mark_persistent(l_Lean_Elab_Command_commandWith__weak__namespace_______closed__17);
l_Lean_Elab_Command_commandWith__weak__namespace_______closed__18 = _init_l_Lean_Elab_Command_commandWith__weak__namespace_______closed__18();
lean_mark_persistent(l_Lean_Elab_Command_commandWith__weak__namespace_______closed__18);
l_Lean_Elab_Command_commandWith__weak__namespace____ = _init_l_Lean_Elab_Command_commandWith__weak__namespace____();
lean_mark_persistent(l_Lean_Elab_Command_commandWith__weak__namespace____);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
