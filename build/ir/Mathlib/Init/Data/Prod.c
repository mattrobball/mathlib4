// Lean compiler output
// Module: Mathlib.Init.Data.Prod
// Imports: Init Mathlib.Init.Logic Mathlib.Util.CompileInductive
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
LEAN_EXPORT lean_object* l_Prod___sizeOf__inst____x40_Mathlib_Init_Data_Prod___hyg_35_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod___sizeOf__1____x40_Mathlib_Init_Data_Prod___hyg_33____rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_rec____x40_Mathlib_Init_Data_Prod___hyg_4____rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod___sizeOf__inst____x40_Mathlib_Init_Data_Prod___hyg_35____elambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_recOn____x40_Mathlib_Init_Data_Prod___hyg_15____rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_recOn____x40_Mathlib_Init_Data_Prod___hyg_15_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod___sizeOf__inst____x40_Mathlib_Init_Data_Prod___hyg_35____rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod___sizeOf__1____x40_Mathlib_Init_Data_Prod___hyg_33____rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod___sizeOf__1____x40_Mathlib_Init_Data_Prod___hyg_33_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_rec____x40_Mathlib_Init_Data_Prod___hyg_4_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod___sizeOf__inst____x40_Mathlib_Init_Data_Prod___hyg_35____elambda__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_rec____x40_Mathlib_Init_Data_Prod___hyg_4____rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_apply_2(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Prod_rec____x40_Mathlib_Init_Data_Prod___hyg_4_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Prod_rec____x40_Mathlib_Init_Data_Prod___hyg_4____rarg), 2, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Prod_recOn____x40_Mathlib_Init_Data_Prod___hyg_15____rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Prod_rec____x40_Mathlib_Init_Data_Prod___hyg_4____rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Prod_recOn____x40_Mathlib_Init_Data_Prod___hyg_15_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Prod_recOn____x40_Mathlib_Init_Data_Prod___hyg_15____rarg), 2, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Prod___sizeOf__1____x40_Mathlib_Init_Data_Prod___hyg_33____rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_apply_1(x_1, x_3);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_6, x_5);
lean_dec(x_5);
x_8 = lean_apply_1(x_2, x_4);
x_9 = lean_nat_add(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Prod___sizeOf__1____x40_Mathlib_Init_Data_Prod___hyg_33____rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Prod___sizeOf__1____x40_Mathlib_Init_Data_Prod___hyg_33____rarg___lambda__1), 4, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
x_5 = l_Prod_rec____x40_Mathlib_Init_Data_Prod___hyg_4____rarg(x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Prod___sizeOf__1____x40_Mathlib_Init_Data_Prod___hyg_33_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Prod___sizeOf__1____x40_Mathlib_Init_Data_Prod___hyg_33____rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Prod___sizeOf__inst____x40_Mathlib_Init_Data_Prod___hyg_35____elambda__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Prod___sizeOf__1____x40_Mathlib_Init_Data_Prod___hyg_33____rarg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Prod___sizeOf__inst____x40_Mathlib_Init_Data_Prod___hyg_35____elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Prod___sizeOf__inst____x40_Mathlib_Init_Data_Prod___hyg_35____elambda__1___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Prod___sizeOf__inst____x40_Mathlib_Init_Data_Prod___hyg_35____rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Prod___sizeOf__inst____x40_Mathlib_Init_Data_Prod___hyg_35____elambda__1___rarg), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Prod___sizeOf__inst____x40_Mathlib_Init_Data_Prod___hyg_35_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Prod___sizeOf__inst____x40_Mathlib_Init_Data_Prod___hyg_35____rarg), 2, 0);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Init_Logic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Util_CompileInductive(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Mathlib_Init_Data_Prod(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Init_Logic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Util_CompileInductive(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
