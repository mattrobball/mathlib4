// Lean compiler output
// Module: Mathlib.Lean.Message
// Imports: Init Lean.Message
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
LEAN_EXPORT lean_object* l_instToMessageDataProd___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_instToMessageDataProd___rarg___closed__3;
static lean_object* l_instToMessageDataProd___rarg___closed__4;
static lean_object* l_instToMessageDataProd___rarg___closed__6;
static lean_object* l_instToMessageDataProd___rarg___closed__1;
LEAN_EXPORT lean_object* l_instToMessageDataProd(lean_object*, lean_object*);
static lean_object* l_instToMessageDataProd___rarg___closed__2;
static lean_object* l_instToMessageDataProd___rarg___closed__5;
lean_object* l_Lean_MessageData_bracket(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_instToMessageDataProd___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(",", 1);
return x_1;
}
}
static lean_object* _init_l_instToMessageDataProd___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instToMessageDataProd___rarg___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_instToMessageDataProd___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instToMessageDataProd___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_instToMessageDataProd___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_instToMessageDataProd___rarg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(", 1);
return x_1;
}
}
static lean_object* _init_l_instToMessageDataProd___rarg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(")", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instToMessageDataProd___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_apply_1(x_1, x_4);
x_6 = l_instToMessageDataProd___rarg___closed__3;
x_7 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_instToMessageDataProd___rarg___closed__4;
x_9 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_apply_1(x_2, x_10);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_instToMessageDataProd___rarg___closed__5;
x_14 = l_instToMessageDataProd___rarg___closed__6;
x_15 = l_Lean_MessageData_bracket(x_13, x_12, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_instToMessageDataProd(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instToMessageDataProd___rarg), 3, 0);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Message(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Mathlib_Lean_Message(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Message(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_instToMessageDataProd___rarg___closed__1 = _init_l_instToMessageDataProd___rarg___closed__1();
lean_mark_persistent(l_instToMessageDataProd___rarg___closed__1);
l_instToMessageDataProd___rarg___closed__2 = _init_l_instToMessageDataProd___rarg___closed__2();
lean_mark_persistent(l_instToMessageDataProd___rarg___closed__2);
l_instToMessageDataProd___rarg___closed__3 = _init_l_instToMessageDataProd___rarg___closed__3();
lean_mark_persistent(l_instToMessageDataProd___rarg___closed__3);
l_instToMessageDataProd___rarg___closed__4 = _init_l_instToMessageDataProd___rarg___closed__4();
lean_mark_persistent(l_instToMessageDataProd___rarg___closed__4);
l_instToMessageDataProd___rarg___closed__5 = _init_l_instToMessageDataProd___rarg___closed__5();
lean_mark_persistent(l_instToMessageDataProd___rarg___closed__5);
l_instToMessageDataProd___rarg___closed__6 = _init_l_instToMessageDataProd___rarg___closed__6();
lean_mark_persistent(l_instToMessageDataProd___rarg___closed__6);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
