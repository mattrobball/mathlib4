// Lean compiler output
// Module: Mathlib.Init.ZeroOne
// Imports: Init Mathlib.Tactic.ToAdditive Mathlib.Mathport.Rename
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
LEAN_EXPORT lean_object* l_Zero_ofOfNat0___rarg(lean_object*);
LEAN_EXPORT lean_object* l_One_toOfNat1___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Zero_ofOfNat0(lean_object*);
LEAN_EXPORT lean_object* l_bit1(lean_object*);
LEAN_EXPORT lean_object* l_One_ofOfNat1___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Zero_toOfNat0___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Zero_toOfNat0___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_bit1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_One_ofOfNat1___rarg(lean_object*);
LEAN_EXPORT lean_object* l_One_toOfNat1(lean_object*);
LEAN_EXPORT lean_object* l_bit0(lean_object*);
LEAN_EXPORT lean_object* l_Zero_toOfNat0(lean_object*);
LEAN_EXPORT lean_object* l_One_toOfNat1___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_One_ofOfNat1(lean_object*);
LEAN_EXPORT lean_object* l_Zero_ofOfNat0___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_bit0___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Zero_toOfNat0___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Zero_toOfNat0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Zero_toOfNat0___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Zero_toOfNat0___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Zero_toOfNat0___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Zero_ofOfNat0___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Zero_ofOfNat0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Zero_ofOfNat0___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Zero_ofOfNat0___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Zero_ofOfNat0___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_One_toOfNat1___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_One_toOfNat1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_One_toOfNat1___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_One_toOfNat1___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_One_toOfNat1___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_One_ofOfNat1___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_One_ofOfNat1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_One_ofOfNat1___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_One_ofOfNat1___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_One_ofOfNat1___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_bit0___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_2);
x_3 = lean_apply_2(x_1, x_2, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_bit0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_bit0___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_bit1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
lean_inc(x_2);
lean_inc(x_3);
x_4 = lean_apply_2(x_2, x_3, x_3);
x_5 = lean_apply_2(x_2, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_bit1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_bit1___rarg), 3, 0);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic_ToAdditive(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Mathport_Rename(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Mathlib_Init_ZeroOne(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic_ToAdditive(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Mathport_Rename(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
