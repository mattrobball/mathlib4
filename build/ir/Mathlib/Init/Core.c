// Lean compiler output
// Module: Mathlib.Init.Core
// Imports: Init Mathlib.Mathport.Rename Std.Classes.SetNotation Std.Classes.Dvd Mathlib.Tactic.Relation.Rfl Mathlib.Tactic.Relation.Symm Mathlib.Tactic.Relation.Trans
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
LEAN_EXPORT lean_object* l_Combinator_K(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_mk_injArrow___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Combinator_I___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Prec_arrow;
LEAN_EXPORT lean_object* l_Prod_mk_injArrow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Priority_max;
LEAN_EXPORT lean_object* l_Prod_mk_injArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_prio;
LEAN_EXPORT lean_object* l_Combinator_I___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_PProd_mk_injArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Prec_maxPlus;
static lean_object* l_Std_Prec_maxPlus___closed__1;
LEAN_EXPORT lean_object* l_Combinator_S___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_prio___closed__1;
LEAN_EXPORT lean_object* l_Combinator_K___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Prec_max;
LEAN_EXPORT lean_object* l_Std_Priority_default;
LEAN_EXPORT lean_object* l_PProd_mk_injArrow___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Combinator_I(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PProd_mk_injArrow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Combinator_K___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Combinator_S(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_mk_injArrow___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_apply_2(x_1, lean_box(0), lean_box(0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_Prod_mk_injArrow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_closure((void*)(l_Prod_mk_injArrow___rarg), 1, 0);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Prod_mk_injArrow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Prod_mk_injArrow(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_PProd_mk_injArrow___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_apply_2(x_1, lean_box(0), lean_box(0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_PProd_mk_injArrow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_closure((void*)(l_PProd_mk_injArrow___rarg), 1, 0);
return x_9;
}
}
LEAN_EXPORT lean_object* l_PProd_mk_injArrow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_PProd_mk_injArrow(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
static lean_object* _init_l_Std_Priority_default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(1000u);
return x_1;
}
}
static lean_object* _init_l_Std_Priority_max() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(4294967295u);
return x_1;
}
}
static lean_object* _init_l_Nat_prio___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Priority_default;
x_2 = lean_unsigned_to_nat(100u);
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Nat_prio() {
_start:
{
lean_object* x_1; 
x_1 = l_Nat_prio___closed__1;
return x_1;
}
}
static lean_object* _init_l_Std_Prec_max() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(1024u);
return x_1;
}
}
static lean_object* _init_l_Std_Prec_arrow() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(25u);
return x_1;
}
}
static lean_object* _init_l_Std_Prec_maxPlus___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Prec_max;
x_2 = lean_unsigned_to_nat(10u);
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Prec_maxPlus() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Prec_maxPlus___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Combinator_I___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Combinator_I(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Combinator_I___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Combinator_I___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Combinator_I___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Combinator_K___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Combinator_K(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Combinator_K___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Combinator_K___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Combinator_K___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Combinator_S___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
lean_inc(x_3);
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_2(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Combinator_S(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Combinator_S___rarg), 3, 0);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Mathport_Rename(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Classes_SetNotation(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Classes_Dvd(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic_Relation_Rfl(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic_Relation_Symm(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic_Relation_Trans(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Mathlib_Init_Core(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Mathport_Rename(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Classes_SetNotation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Classes_Dvd(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic_Relation_Rfl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic_Relation_Symm(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic_Relation_Trans(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Priority_default = _init_l_Std_Priority_default();
lean_mark_persistent(l_Std_Priority_default);
l_Std_Priority_max = _init_l_Std_Priority_max();
lean_mark_persistent(l_Std_Priority_max);
l_Nat_prio___closed__1 = _init_l_Nat_prio___closed__1();
lean_mark_persistent(l_Nat_prio___closed__1);
l_Nat_prio = _init_l_Nat_prio();
lean_mark_persistent(l_Nat_prio);
l_Std_Prec_max = _init_l_Std_Prec_max();
lean_mark_persistent(l_Std_Prec_max);
l_Std_Prec_arrow = _init_l_Std_Prec_arrow();
lean_mark_persistent(l_Std_Prec_arrow);
l_Std_Prec_maxPlus___closed__1 = _init_l_Std_Prec_maxPlus___closed__1();
lean_mark_persistent(l_Std_Prec_maxPlus___closed__1);
l_Std_Prec_maxPlus = _init_l_Std_Prec_maxPlus();
lean_mark_persistent(l_Std_Prec_maxPlus);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
