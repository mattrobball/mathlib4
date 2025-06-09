// Lean compiler output
// Module: Mathlib.Util.Syntax
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
static lean_object* l_Lean_TSyntax_replaceM___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_TSyntax_replaceM___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_replaceM___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_replaceM(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_replaceM___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_replaceM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_replaceM___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_replaceM___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lean_TSyntax_replaceM___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_TSyntax_replaceM___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_replaceM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Syntax_replaceM___rarg(x_1, x_2, x_3);
x_8 = l_Lean_TSyntax_replaceM___rarg___closed__1;
x_9 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_replaceM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_TSyntax_replaceM___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_replaceM___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_TSyntax_replaceM___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_replaceM___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_TSyntax_replaceM(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_SepArray_ofElems(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_TSepArray_ofElems___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_TSepArray_ofElems___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_TSepArray_ofElems(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Mathlib_Util_Syntax(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_TSyntax_replaceM___rarg___closed__1 = _init_l_Lean_TSyntax_replaceM___rarg___closed__1();
lean_mark_persistent(l_Lean_TSyntax_replaceM___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
