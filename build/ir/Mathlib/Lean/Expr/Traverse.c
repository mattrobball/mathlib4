// Lean compiler output
// Module: Mathlib.Lean.Expr.Traverse
// Imports: Init Lean Mathlib.Lean.Expr.Basic
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
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___rarg___lambda__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___rarg___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Expr_updateForallE_x21(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_foldlM___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___rarg___lambda__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___rarg___lambda__1(lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateLambdaE_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__4(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__4___closed__1;
static lean_object* l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__3___closed__4;
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at_Lean_Expr_getRevArg_x21___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__4___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__3___closed__2;
static lean_object* l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__4___closed__2;
lean_object* l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 5:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed), 3, 1);
lean_closure_set(x_8, 0, x_3);
x_9 = lean_apply_2(x_7, lean_box(0), x_8);
lean_inc(x_2);
x_10 = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_4);
lean_inc(x_6);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_5);
x_13 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
case 6:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_alloc_closure((void*)(l_Lean_Expr_updateLambdaE_x21), 3, 1);
lean_closure_set(x_18, 0, x_3);
x_19 = lean_apply_2(x_17, lean_box(0), x_18);
lean_inc(x_2);
x_20 = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_20, 0, x_2);
lean_closure_set(x_20, 1, x_14);
lean_inc(x_16);
x_21 = lean_apply_4(x_16, lean_box(0), lean_box(0), x_19, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_22, 0, x_2);
lean_closure_set(x_22, 1, x_15);
x_23 = lean_apply_4(x_16, lean_box(0), lean_box(0), x_21, x_22);
return x_23;
}
case 7:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_ctor_get(x_3, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_3, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 2);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_dec(x_1);
x_28 = lean_alloc_closure((void*)(l_Lean_Expr_updateForallE_x21), 3, 1);
lean_closure_set(x_28, 0, x_3);
x_29 = lean_apply_2(x_27, lean_box(0), x_28);
lean_inc(x_2);
x_30 = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_30, 0, x_2);
lean_closure_set(x_30, 1, x_24);
lean_inc(x_26);
x_31 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_29, x_30);
x_32 = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_32, 0, x_2);
lean_closure_set(x_32, 1, x_25);
x_33 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_31, x_32);
return x_33;
}
case 8:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_34 = lean_ctor_get(x_3, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_3, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_3, 3);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 2);
lean_inc(x_37);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
lean_dec(x_1);
x_39 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl), 4, 1);
lean_closure_set(x_39, 0, x_3);
x_40 = lean_apply_2(x_38, lean_box(0), x_39);
lean_inc(x_2);
x_41 = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_41, 0, x_2);
lean_closure_set(x_41, 1, x_34);
lean_inc(x_37);
x_42 = lean_apply_4(x_37, lean_box(0), lean_box(0), x_40, x_41);
lean_inc(x_2);
x_43 = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_43, 0, x_2);
lean_closure_set(x_43, 1, x_35);
lean_inc(x_37);
x_44 = lean_apply_4(x_37, lean_box(0), lean_box(0), x_42, x_43);
x_45 = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_45, 0, x_2);
lean_closure_set(x_45, 1, x_36);
x_46 = lean_apply_4(x_37, lean_box(0), lean_box(0), x_44, x_45);
return x_46;
}
case 10:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_3, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
lean_dec(x_1);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl), 2, 1);
lean_closure_set(x_50, 0, x_3);
x_51 = lean_apply_1(x_2, x_47);
x_52 = lean_apply_4(x_49, lean_box(0), lean_box(0), x_50, x_51);
return x_52;
}
case 11:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_3, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_1, 0);
lean_inc(x_54);
lean_dec(x_1);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl), 2, 1);
lean_closure_set(x_56, 0, x_3);
x_57 = lean_apply_1(x_2, x_53);
x_58 = lean_apply_4(x_55, lean_box(0), lean_box(0), x_56, x_57);
return x_58;
}
default: 
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_2);
x_59 = lean_ctor_get(x_1, 1);
lean_inc(x_59);
lean_dec(x_1);
x_60 = lean_apply_2(x_59, lean_box(0), x_3);
return x_60;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_traverseChildren___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_apply_1(x_1, x_5);
lean_ctor_set(x_3, 0, x_6);
x_7 = lean_apply_2(x_2, lean_box(0), x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_10 = lean_apply_1(x_1, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = lean_apply_2(x_2, lean_box(0), x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_apply_2(x_1, x_2, x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__1), 3, 2);
lean_closure_set(x_9, 0, x_6);
lean_closure_set(x_9, 1, x_3);
x_10 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
static lean_object* _init_l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Expr", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_private.Lean.Expr.0.Lean.Expr.updateMData!Impl", 47);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("mdata expected", 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__3___closed__1;
x_2 = l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__3___closed__2;
x_3 = lean_unsigned_to_nat(1507u);
x_4 = lean_unsigned_to_nat(17u);
x_5 = l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__3___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 10)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; uint8_t x_12; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
x_10 = lean_ptr_addr(x_9);
lean_dec(x_9);
x_11 = lean_ptr_addr(x_5);
x_12 = lean_usize_dec_eq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_13 = l_Lean_Expr_mdata___override(x_8, x_5);
lean_ctor_set(x_3, 0, x_13);
x_14 = lean_apply_2(x_7, lean_box(0), x_3);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_2);
x_15 = lean_apply_2(x_7, lean_box(0), x_3);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; uint8_t x_24; 
x_16 = lean_ctor_get(x_3, 0);
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_3);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
x_22 = lean_ptr_addr(x_21);
lean_dec(x_21);
x_23 = lean_ptr_addr(x_16);
x_24 = lean_usize_dec_eq(x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_2);
x_25 = l_Lean_Expr_mdata___override(x_20, x_16);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_17);
x_27 = lean_apply_2(x_19, lean_box(0), x_26);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_20);
lean_dec(x_16);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_17);
x_29 = lean_apply_2(x_19, lean_box(0), x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_3);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_3, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
lean_dec(x_1);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__3___closed__4;
x_35 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_34);
lean_ctor_set(x_3, 0, x_35);
x_36 = lean_apply_2(x_33, lean_box(0), x_3);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_3, 1);
lean_inc(x_37);
lean_dec(x_3);
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
lean_dec(x_1);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__3___closed__4;
x_41 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_37);
x_43 = lean_apply_2(x_39, lean_box(0), x_42);
return x_43;
}
}
}
}
static lean_object* _init_l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_private.Lean.Expr.0.Lean.Expr.updateProj!Impl", 46);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("proj expected", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__3___closed__1;
x_2 = l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__4___closed__1;
x_3 = lean_unsigned_to_nat(1518u);
x_4 = lean_unsigned_to_nat(18u);
x_5 = l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__4___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 11)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; uint8_t x_13; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
x_11 = lean_ptr_addr(x_10);
lean_dec(x_10);
x_12 = lean_ptr_addr(x_5);
x_13 = lean_usize_dec_eq(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_14 = l_Lean_Expr_proj___override(x_8, x_9, x_5);
lean_ctor_set(x_3, 0, x_14);
x_15 = lean_apply_2(x_7, lean_box(0), x_3);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_2);
x_16 = lean_apply_2(x_7, lean_box(0), x_3);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; uint8_t x_26; 
x_17 = lean_ctor_get(x_3, 0);
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_3);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 2);
lean_inc(x_23);
x_24 = lean_ptr_addr(x_23);
lean_dec(x_23);
x_25 = lean_ptr_addr(x_17);
x_26 = lean_usize_dec_eq(x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_2);
x_27 = l_Lean_Expr_proj___override(x_21, x_22, x_17);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_18);
x_29 = lean_apply_2(x_20, lean_box(0), x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_17);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_18);
x_31 = lean_apply_2(x_20, lean_box(0), x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_3);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_3, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
lean_dec(x_1);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__4___closed__3;
x_37 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_36);
lean_ctor_set(x_3, 0, x_37);
x_38 = lean_apply_2(x_35, lean_box(0), x_3);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_3, 1);
lean_inc(x_39);
lean_dec(x_3);
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
lean_dec(x_1);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__4___closed__3;
x_43 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_39);
x_45 = lean_apply_2(x_41, lean_box(0), x_44);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 5:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed), 3, 1);
lean_closure_set(x_7, 0, x_3);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_4);
lean_inc(x_10);
x_12 = lean_apply_2(x_10, lean_box(0), x_11);
lean_inc(x_8);
lean_inc(x_10);
lean_inc(x_2);
x_13 = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__2), 5, 4);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_5);
lean_closure_set(x_13, 2, x_10);
lean_closure_set(x_13, 3, x_8);
lean_inc(x_8);
x_14 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_12, x_13);
lean_inc(x_8);
x_15 = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__2), 5, 4);
lean_closure_set(x_15, 0, x_2);
lean_closure_set(x_15, 1, x_6);
lean_closure_set(x_15, 2, x_10);
lean_closure_set(x_15, 3, x_8);
x_16 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_14, x_15);
return x_16;
}
case 6:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 2);
lean_inc(x_18);
x_19 = lean_alloc_closure((void*)(l_Lean_Expr_updateLambdaE_x21), 3, 1);
lean_closure_set(x_19, 0, x_3);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_4);
lean_inc(x_22);
x_24 = lean_apply_2(x_22, lean_box(0), x_23);
lean_inc(x_20);
lean_inc(x_22);
lean_inc(x_2);
x_25 = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__2), 5, 4);
lean_closure_set(x_25, 0, x_2);
lean_closure_set(x_25, 1, x_17);
lean_closure_set(x_25, 2, x_22);
lean_closure_set(x_25, 3, x_20);
lean_inc(x_20);
x_26 = lean_apply_4(x_20, lean_box(0), lean_box(0), x_24, x_25);
lean_inc(x_20);
x_27 = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__2), 5, 4);
lean_closure_set(x_27, 0, x_2);
lean_closure_set(x_27, 1, x_18);
lean_closure_set(x_27, 2, x_22);
lean_closure_set(x_27, 3, x_20);
x_28 = lean_apply_4(x_20, lean_box(0), lean_box(0), x_26, x_27);
return x_28;
}
case 7:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_29 = lean_ctor_get(x_3, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_3, 2);
lean_inc(x_30);
x_31 = lean_alloc_closure((void*)(l_Lean_Expr_updateForallE_x21), 3, 1);
lean_closure_set(x_31, 0, x_3);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
lean_dec(x_1);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_4);
lean_inc(x_34);
x_36 = lean_apply_2(x_34, lean_box(0), x_35);
lean_inc(x_32);
lean_inc(x_34);
lean_inc(x_2);
x_37 = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__2), 5, 4);
lean_closure_set(x_37, 0, x_2);
lean_closure_set(x_37, 1, x_29);
lean_closure_set(x_37, 2, x_34);
lean_closure_set(x_37, 3, x_32);
lean_inc(x_32);
x_38 = lean_apply_4(x_32, lean_box(0), lean_box(0), x_36, x_37);
lean_inc(x_32);
x_39 = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__2), 5, 4);
lean_closure_set(x_39, 0, x_2);
lean_closure_set(x_39, 1, x_30);
lean_closure_set(x_39, 2, x_34);
lean_closure_set(x_39, 3, x_32);
x_40 = lean_apply_4(x_32, lean_box(0), lean_box(0), x_38, x_39);
return x_40;
}
case 8:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_41 = lean_ctor_get(x_3, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_3, 2);
lean_inc(x_42);
x_43 = lean_ctor_get(x_3, 3);
lean_inc(x_43);
x_44 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl), 4, 1);
lean_closure_set(x_44, 0, x_3);
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_1, 0);
lean_inc(x_46);
lean_dec(x_1);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_44);
lean_ctor_set(x_48, 1, x_4);
lean_inc(x_47);
x_49 = lean_apply_2(x_47, lean_box(0), x_48);
lean_inc(x_45);
lean_inc(x_47);
lean_inc(x_2);
x_50 = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__2), 5, 4);
lean_closure_set(x_50, 0, x_2);
lean_closure_set(x_50, 1, x_41);
lean_closure_set(x_50, 2, x_47);
lean_closure_set(x_50, 3, x_45);
lean_inc(x_45);
x_51 = lean_apply_4(x_45, lean_box(0), lean_box(0), x_49, x_50);
lean_inc(x_45);
lean_inc(x_47);
lean_inc(x_2);
x_52 = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__2), 5, 4);
lean_closure_set(x_52, 0, x_2);
lean_closure_set(x_52, 1, x_42);
lean_closure_set(x_52, 2, x_47);
lean_closure_set(x_52, 3, x_45);
lean_inc(x_45);
x_53 = lean_apply_4(x_45, lean_box(0), lean_box(0), x_51, x_52);
lean_inc(x_45);
x_54 = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__2), 5, 4);
lean_closure_set(x_54, 0, x_2);
lean_closure_set(x_54, 1, x_43);
lean_closure_set(x_54, 2, x_47);
lean_closure_set(x_54, 3, x_45);
x_55 = lean_apply_4(x_45, lean_box(0), lean_box(0), x_53, x_54);
return x_55;
}
case 10:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_3, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_1, 1);
lean_inc(x_57);
x_58 = lean_apply_2(x_2, x_56, x_4);
x_59 = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__3), 3, 2);
lean_closure_set(x_59, 0, x_1);
lean_closure_set(x_59, 1, x_3);
x_60 = lean_apply_4(x_57, lean_box(0), lean_box(0), x_58, x_59);
return x_60;
}
case 11:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_3, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_1, 1);
lean_inc(x_62);
x_63 = lean_apply_2(x_2, x_61, x_4);
x_64 = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__4), 3, 2);
lean_closure_set(x_64, 0, x_1);
lean_closure_set(x_64, 1, x_3);
x_65 = lean_apply_4(x_62, lean_box(0), lean_box(0), x_63, x_64);
return x_65;
}
default: 
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_2);
x_66 = lean_ctor_get(x_1, 0);
lean_inc(x_66);
lean_dec(x_1);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_3);
lean_ctor_set(x_68, 1, x_4);
x_69 = lean_apply_2(x_67, lean_box(0), x_68);
return x_69;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_apply_2(x_1, x_6, x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___rarg___lambda__2), 3, 2);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_3);
x_10 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___rarg___lambda__4(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_dec(x_5);
x_6 = lean_box(0);
lean_ctor_set(x_2, 1, x_4);
lean_ctor_set(x_2, 0, x_6);
x_7 = lean_apply_2(x_1, lean_box(0), x_2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_apply_2(x_1, lean_box(0), x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_1);
x_6 = lean_apply_2(x_2, lean_box(0), x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_apply_2(x_2, lean_box(0), x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___rarg___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
lean_inc(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_5);
lean_inc(x_7);
x_9 = lean_apply_2(x_7, lean_box(0), x_8);
lean_inc(x_6);
lean_inc(x_7);
lean_inc(x_4);
x_10 = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___rarg___lambda__3), 5, 4);
lean_closure_set(x_10, 0, x_3);
lean_closure_set(x_10, 1, x_4);
lean_closure_set(x_10, 2, x_7);
lean_closure_set(x_10, 3, x_6);
lean_inc(x_6);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_10);
lean_inc(x_7);
x_12 = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___rarg___lambda__4), 2, 1);
lean_closure_set(x_12, 0, x_7);
lean_inc(x_6);
x_13 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_11, x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___rarg___lambda__5), 3, 2);
lean_closure_set(x_14, 0, x_4);
lean_closure_set(x_14, 1, x_7);
x_15 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
static lean_object* _init_l_Lean_Expr_foldlM___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___rarg___lambda__6), 5, 3);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_5);
lean_closure_set(x_8, 2, x_2);
x_9 = l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg(x_1, x_8, x_4, x_3);
x_10 = l_Lean_Expr_foldlM___rarg___closed__1;
x_11 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_10, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_foldlM___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Lean_Expr_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Mathlib_Lean_Expr_Traverse(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Lean_Expr_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__3___closed__1 = _init_l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__3___closed__1);
l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__3___closed__2 = _init_l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__3___closed__2);
l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__3___closed__3 = _init_l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__3___closed__3);
l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__3___closed__4 = _init_l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__3___closed__4);
l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__4___closed__1 = _init_l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__4___closed__1);
l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__4___closed__2 = _init_l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__4___closed__2);
l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__4___closed__3 = _init_l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__4___closed__3();
lean_mark_persistent(l_Lean_Expr_traverseChildren___at_Lean_Expr_foldlM___spec__1___rarg___lambda__4___closed__3);
l_Lean_Expr_foldlM___rarg___closed__1 = _init_l_Lean_Expr_foldlM___rarg___closed__1();
lean_mark_persistent(l_Lean_Expr_foldlM___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
