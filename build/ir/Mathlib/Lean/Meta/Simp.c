// Lean compiler output
// Module: Mathlib.Lean.Meta.Simp
// Imports: Init Lean Std.Tactic.OpenPrivate
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
static lean_object* l_Lean_Meta_simpTheoremsOfNames___closed__1;
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_simpTheoremsOfNames___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_mkSimpContext_x27___closed__1;
lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_addSimpAttrFromSyntax___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_simpType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getAttrParamOptPrio(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getElements___spec__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimpAttrFromSyntax___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__9;
static lean_object* l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__1;
static lean_object* l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkDischargeWrapper___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__11;
static lean_object* l_Lean_Meta_simpEq___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_HashMap_toList___at_Lean_Meta_getAllSimpAttrs___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_getPropHyps___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_Lean_Meta_DiscrTree_getElements___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Meta_getAllSimpAttrs___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_getElements___rarg(uint8_t, lean_object*);
static lean_object* l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__3;
static lean_object* l_Lean_Meta_simpEq___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_Trie_getElements___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__17(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__7;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__14(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Meta_Simp_mkSimpTheoremsFromConst_x27___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__9;
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__4(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_Meta_Simp_mkSimpContext_x27___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_getAllSimpDecls(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_addSimpAttrFromSyntax___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_simpEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentHashMap_empty___at_Lean_KeyedDeclsAttribute_ExtensionState_declNames___default___spec__1;
static lean_object* l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_PHashSet_toList___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__5(lean_object*);
lean_object* l_Lean_Meta_mkExpectedTypeHint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__15(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_simpEq___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getElements___spec__3(lean_object*);
static lean_object* l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__8;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_getPropHyps___spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_Simp_getPropHyps___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimpContext_x27___lambda__1(lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__2;
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_hasValue(lean_object*);
static lean_object* l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_simpEq___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_elabSimpConfig(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__3;
static lean_object* l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__12;
static lean_object* l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getElements___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t l_Lean_Meta_hasSmartUnfoldingDecl(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_SimpTheorems_isLemma(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_ofNames___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_mkSimpContext_x27___lambda__3___closed__1;
static lean_object* l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__10;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getElements___spec__2(lean_object*, uint8_t);
lean_object* l_Lean_Meta_getSimpCongrTheorems___rarg(lean_object*, lean_object*);
static lean_object* l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__3;
LEAN_EXPORT lean_object* l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__16(lean_object*);
extern lean_object* l_Lean_PersistentHashMap_empty___at_Lean_Meta_SimpTheorems_lemmaNames___default___spec__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkDischargeWrapper(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(lean_object*, lean_object*);
static lean_object* l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__4;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_getPropHyps___spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_Lean_Meta_DiscrTree_getElements___spec__1___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimpContext_x27(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxLemma(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_Trie_getElements___spec__1___rarg(uint8_t, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_mkEqMP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PHashSet_toList___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Meta_getAllSimpAttrs___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpTheoremCore(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimpTheorem_x27(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Simp_addSimpAttr___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_SimpTheorems_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PHashSet_toList(lean_object*);
static lean_object* l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__4;
static lean_object* l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__11;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Meta_getAllSimpAttrs___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_contains___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_Simp_getPropHyps___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_simpEq___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instToFormatSimpTheorems(lean_object*);
static lean_object* l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__9;
static lean_object* l_Lean_Meta_Simp_addSimpAttrFromSyntax___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_checkTypeIsProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__4;
lean_object* l_Lean_Meta_Origin_key(lean_object*);
lean_object* l_Lean_Meta_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Simp_addSimpAttr___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isInSimpSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_Trie_getElements___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___at_Lean_Elab_Tactic_mkSimpContext___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__4;
lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*, uint8_t);
lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getAllSimpAttrs___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_simpEq___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_simpEq___lambda__1___closed__2;
lean_object* lean_array_to_list(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_addSimpAttrFromSyntax___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_ofNames(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_addSimpAttrFromSyntax___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_Simp_getPropHyps___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_Lean_Meta_DiscrTree_getElements___spec__1(lean_object*);
static lean_object* l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimpAttrFromSyntax(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getElements___rarg(uint8_t, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_Trie_getElements___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimpAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_addSimpAttr___closed__1;
extern lean_object* l_Lean_Meta_simpExtension;
lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimpTheoremsFromConst_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_getAllSimpAttrs___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__5;
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
lean_object* l_Lean_PersistentHashMap_toList___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__8;
LEAN_EXPORT lean_object* l_List_filterMap___at_Lean_Meta_getAllSimpDecls___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Meta_Simp_mkSimpTheoremsFromConst_x27___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_PHashSet_toList___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__10(lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getPropHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__1;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__9(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpExtension_getTheorems(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimpContext_x27___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimpTheorem_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_addSimpAttr___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_getPropHyps___spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimpContext_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_preprocess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_addSimpTheorem_x27___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__5;
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_shouldPreprocess___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_Simp_getPropHyps___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_getElements(lean_object*);
uint8_t l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_beqSimpKind____x40_Lean_Elab_Tactic_Simp___hyg_814_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_Simp_getPropHyps___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3___closed__1;
lean_object* lean_string_length(lean_object*);
static lean_object* l_Lean_Meta_Simp_mkSimpTheoremsFromConst_x27___closed__1;
static lean_object* l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__3;
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_simpTheoremsOfNames___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_getAllSimpAttrs___spec__3(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_getPropHyps___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_simpOnlyNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isInSimpSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_getPropHyps___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_Simp_getPropHyps___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_toList___at_Lean_Meta_DiscrTree_getElements___spec__1___rarg___closed__1;
static lean_object* l_Lean_Meta_Simp_mkCast___closed__1;
static lean_object* l_Lean_Meta_Simp_mkCast___closed__2;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__8(lean_object*, lean_object*);
lean_object* l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4(lean_object*);
static lean_object* l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__11;
lean_object* l_Lean_Meta_getSimpExtension_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimpAttr(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimpTheoremsFromConst_x27(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_mkSimpContext_x27___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_PHashSet_toList___spec__1___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_mkCast___closed__3;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_SimpTheorems_isDeclToUnfold(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_simpTheoremsOfNames(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_getAllSimpAttrs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getElements___spec__2___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getElements___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__2;
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Meta_getAllSimpAttrs___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_getElements___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_mkCalcTrans___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimpContext_x27___lambda__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__8;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpContext___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpTheorems_addConst(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_simpEq___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_preprocess(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_simpOnlyNames___closed__1;
lean_object* l_Lean_mkHashMapImp___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getElements___spec__3___rarg(uint8_t, lean_object*, size_t, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__5;
extern lean_object* l_Lean_Meta_simpExtensionMapRef;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__13(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_shouldPreprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_addSimpAttr___spec__2(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpTheoremCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getAllSimpAttrs___closed__1;
lean_object* l_List_redLength___rarg(lean_object*);
static lean_object* l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__10;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_PHashSet_toList___spec__1(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3___closed__3;
lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_mkDischargeWrapper(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_mkSimpContext_x27___closed__2;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Elab_Tactic_elabSimpArgs(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__2(lean_object*, lean_object*);
static lean_object* l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_addSimpAttr___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_addSimpTheorem_x27___spec__1(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimpContext_x27___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getAllSimpDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__7;
lean_object* l_Nat_repr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getElements(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_Lean_Meta_DiscrTree_getElements___spec__1___rarg(uint8_t, lean_object*);
static lean_object* l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__6;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__11(lean_object*);
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
static lean_object* l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3___closed__6;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_PHashSet_toList___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_PHashSet_toList___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_mapTR_loop___at_Lean_PHashSet_toList___spec__1___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PHashSet_toList___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_PersistentHashMap_toList___rarg(x_1, x_2, x_3);
x_5 = lean_box(0);
x_6 = l_List_mapTR_loop___at_Lean_PHashSet_toList___spec__1___rarg(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PHashSet_toList(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PHashSet_toList___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_Trie_getElements___spec__1___rarg(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l_Lean_Meta_DiscrTree_Trie_getElements___rarg(x_1, x_10);
x_12 = l_Array_append___rarg(x_5, x_11);
x_3 = x_9;
x_5 = x_12;
goto _start;
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_Trie_getElements___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_Trie_getElements___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Trie_getElements___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_getElements___rarg(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = l_Lean_Meta_DiscrTree_Trie_getElements___rarg___closed__1;
x_9 = l_Array_append___rarg(x_3, x_8);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_5, x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_4);
x_11 = l_Lean_Meta_DiscrTree_Trie_getElements___rarg___closed__1;
x_12 = l_Array_append___rarg(x_3, x_11);
return x_12;
}
else
{
size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = 0;
x_14 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_15 = l_Lean_Meta_DiscrTree_Trie_getElements___rarg___closed__1;
x_16 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_Trie_getElements___spec__1___rarg(x_1, x_4, x_13, x_14, x_15);
lean_dec(x_4);
x_17 = l_Array_append___rarg(x_3, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_getElements(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_getElements___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_Trie_getElements___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_Trie_getElements___spec__1___rarg(x_6, x_2, x_7, x_8, x_5);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_getElements___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Meta_DiscrTree_Trie_getElements___rarg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getElements___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___rarg(x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getElements___spec__2(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getElements___spec__2___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_Lean_Meta_DiscrTree_getElements___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_toList___at_Lean_Meta_DiscrTree_getElements___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_toList___at_Lean_Meta_DiscrTree_getElements___spec__1___rarg___lambda__1), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_Lean_Meta_DiscrTree_getElements___spec__1___rarg(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = l_Lean_PersistentHashMap_toList___at_Lean_Meta_DiscrTree_getElements___spec__1___rarg___closed__1;
x_5 = l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getElements___spec__2___rarg(x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_Lean_Meta_DiscrTree_getElements___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_toList___at_Lean_Meta_DiscrTree_getElements___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getElements___spec__3___rarg(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l_Lean_Meta_DiscrTree_Trie_getElements___rarg(x_1, x_10);
x_12 = l_Array_append___rarg(x_5, x_11);
x_3 = x_9;
x_5 = x_12;
goto _start;
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getElements___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getElements___spec__3___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getElements___rarg(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = l_Lean_PersistentHashMap_toList___at_Lean_Meta_DiscrTree_getElements___spec__1___rarg(x_1, x_2);
x_4 = l_List_redLength___rarg(x_3);
x_5 = lean_mk_empty_array_with_capacity(x_4);
lean_dec(x_4);
x_6 = l_List_toArrayAux___rarg(x_3, x_5);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
x_10 = l_Lean_Meta_DiscrTree_Trie_getElements___rarg___closed__1;
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_7, x_7);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_6);
x_12 = l_Lean_Meta_DiscrTree_Trie_getElements___rarg___closed__1;
return x_12;
}
else
{
size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
x_13 = 0;
x_14 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_15 = l_Lean_Meta_DiscrTree_Trie_getElements___rarg___closed__1;
x_16 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getElements___spec__3___rarg(x_1, x_6, x_13, x_14, x_15);
lean_dec(x_6);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getElements(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_getElements___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getElements___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_DiscrTree_getElements___spec__2(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_Lean_Meta_DiscrTree_getElements___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_PersistentHashMap_toList___at_Lean_Meta_DiscrTree_getElements___spec__1___rarg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getElements___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_DiscrTree_getElements___spec__3___rarg(x_6, x_2, x_7, x_8, x_5);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getElements___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Meta_DiscrTree_getElements___rarg(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":", 1);
return x_1;
}
}
static lean_object* _init_l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":perm", 5);
return x_1;
}
}
static lean_object* _init_l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3___closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
lean_inc(x_1);
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_1);
x_7 = lean_ctor_get_uint8(x_4, sizeof(void*)*5 + 1);
x_8 = lean_ctor_get(x_4, 4);
lean_inc(x_8);
x_9 = l_Lean_Meta_Origin_key(x_8);
lean_dec(x_8);
x_10 = 1;
x_11 = l_Lean_Name_toString(x_9, x_10);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_ctor_get(x_4, 3);
lean_inc(x_13);
lean_dec(x_4);
x_14 = l_Nat_repr(x_13);
x_15 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3___closed__2;
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3___closed__4;
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
if (x_7 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
x_22 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_22, 0, x_6);
lean_ctor_set(x_22, 1, x_21);
x_2 = x_22;
x_3 = x_5;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3___closed__6;
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_6);
lean_ctor_set(x_26, 1, x_25);
x_2 = x_26;
x_3 = x_5;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
lean_inc(x_1);
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_1);
x_7 = lean_ctor_get_uint8(x_4, sizeof(void*)*5 + 1);
x_8 = lean_ctor_get(x_4, 4);
lean_inc(x_8);
x_9 = l_Lean_Meta_Origin_key(x_8);
lean_dec(x_8);
x_10 = 1;
x_11 = l_Lean_Name_toString(x_9, x_10);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_ctor_get(x_4, 3);
lean_inc(x_13);
lean_dec(x_4);
x_14 = l_Nat_repr(x_13);
x_15 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3___closed__2;
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3___closed__4;
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
if (x_7 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
x_22 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_22, 0, x_6);
lean_ctor_set(x_22, 1, x_21);
x_2 = x_22;
x_3 = x_5;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3___closed__6;
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_6);
lean_ctor_set(x_26, 1, x_25);
x_2 = x_26;
x_3 = x_5;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get_uint8(x_5, sizeof(void*)*5 + 1);
x_7 = lean_ctor_get(x_5, 4);
lean_inc(x_7);
x_8 = l_Lean_Meta_Origin_key(x_7);
lean_dec(x_7);
x_9 = 1;
x_10 = l_Lean_Name_toString(x_8, x_9);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_ctor_get(x_5, 3);
lean_inc(x_12);
lean_dec(x_5);
x_13 = l_Nat_repr(x_12);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3___closed__2;
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3___closed__4;
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_18);
if (x_6 == 0)
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3___closed__6;
x_22 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
lean_dec(x_1);
x_24 = lean_ctor_get_uint8(x_23, sizeof(void*)*5 + 1);
x_25 = lean_ctor_get(x_23, 4);
lean_inc(x_25);
x_26 = l_Lean_Meta_Origin_key(x_25);
lean_dec(x_25);
x_27 = 1;
x_28 = l_Lean_Name_toString(x_26, x_27);
x_29 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_ctor_get(x_23, 3);
lean_inc(x_30);
lean_dec(x_23);
x_31 = l_Nat_repr(x_30);
x_32 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3___closed__2;
x_34 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3___closed__4;
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_36);
if (x_24 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
x_39 = l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3(x_2, x_38, x_4);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3___closed__6;
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__4(x_2, x_41, x_4);
return x_42;
}
}
}
}
}
static lean_object* _init_l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("[]", 2);
return x_1;
}
}
static lean_object* _init_l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(",", 1);
return x_1;
}
}
static lean_object* _init_l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__4;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("[", 1);
return x_1;
}
}
static lean_object* _init_l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__6;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__7;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__6;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("]", 1);
return x_1;
}
}
static lean_object* _init_l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__10;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__2;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_3 = l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__5;
x_4 = l_Std_Format_joinSep___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__2(x_1, x_3);
x_5 = l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__9;
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
x_7 = l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__11;
x_8 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__8;
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = 0;
x_12 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___rarg(x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = l_Lean_PersistentHashMap_toList___at_Lean_Meta_DiscrTree_getElements___spec__1___rarg___closed__1;
x_4 = l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__7(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__8(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PHashSet_toList___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_PersistentHashMap_toList___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__6(x_1);
x_3 = lean_box(0);
x_4 = l_List_mapTR_loop___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__8(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__9(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Meta_Origin_key(x_5);
lean_dec(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Lean_Meta_Origin_key(x_9);
lean_dec(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___rarg(x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__11(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = l_Lean_PersistentHashMap_toList___at_Lean_Meta_DiscrTree_getElements___spec__1___rarg___closed__1;
x_4 = l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__12(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__13(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PHashSet_toList___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__10(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_PersistentHashMap_toList___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__11(x_1);
x_3 = lean_box(0);
x_4 = l_List_mapTR_loop___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__13(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_mkModuleData___spec__3___rarg(x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__14(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = l_Lean_PersistentHashMap_toList___at_Lean_Meta_DiscrTree_getElements___spec__1___rarg___closed__1;
x_4 = l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__15(x_1, x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("#", 1);
return x_1;
}
}
static lean_object* _init_l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(", 1);
return x_1;
}
}
static lean_object* _init_l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__3;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__4;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(")", 1);
return x_1;
}
}
static lean_object* _init_l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__7;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
lean_inc(x_1);
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_1);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
x_9 = 1;
x_10 = l_Lean_Name_toString(x_7, x_9);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__4;
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_box(1);
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_array_to_list(lean_box(0), x_8);
x_17 = l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4(x_16);
x_18 = l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__2;
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__6;
x_22 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__8;
x_24 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__5;
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = 0;
x_28 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_6);
lean_ctor_set(x_29, 1, x_28);
x_2 = x_29;
x_3 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__17(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = 1;
x_9 = l_Lean_Name_toString(x_6, x_8);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__4;
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_box(1);
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_array_to_list(lean_box(0), x_7);
x_16 = l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4(x_15);
x_17 = l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__2;
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__6;
x_21 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__8;
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__5;
x_25 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = 0;
x_27 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_26);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
lean_dec(x_1);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = 1;
x_32 = l_Lean_Name_toString(x_29, x_31);
x_33 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__4;
x_35 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_box(1);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_array_to_list(lean_box(0), x_30);
x_39 = l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4(x_38);
x_40 = l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__2;
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_37);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__6;
x_44 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__8;
x_46 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__5;
x_48 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = 0;
x_50 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set_uint8(x_50, sizeof(void*)*1, x_49);
x_51 = l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18(x_2, x_50, x_4);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__16(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__2;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_3 = l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__5;
x_4 = l_Std_Format_joinSep___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__17(x_1, x_3);
x_5 = l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__9;
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
x_7 = l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__11;
x_8 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__8;
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = 0;
x_12 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_11);
return x_12;
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("pre:\n", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\npost:\n", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nlemmaNames:\n", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\ntoUnfold: ", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__7;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nerased: ", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__9;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\ntoUnfoldThms: ", 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__11;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instToFormatSimpTheorems(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = 1;
x_4 = l_Lean_Meta_DiscrTree_getElements___rarg(x_3, x_2);
x_5 = lean_array_to_list(lean_box(0), x_4);
x_6 = l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1(x_5);
x_7 = l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__2;
x_8 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__4;
x_10 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = l_Lean_Meta_DiscrTree_getElements___rarg(x_3, x_11);
x_13 = lean_array_to_list(lean_box(0), x_12);
x_14 = l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1(x_13);
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__6;
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_ctor_get(x_1, 2);
lean_inc(x_18);
x_19 = l_Lean_PHashSet_toList___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__5(x_18);
x_20 = lean_box(0);
x_21 = l_List_mapTR_loop___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__9(x_19, x_20);
x_22 = l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4(x_21);
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__8;
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_ctor_get(x_1, 3);
lean_inc(x_26);
x_27 = l_Lean_PHashSet_toList___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__10(x_26);
x_28 = l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4(x_27);
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__10;
x_31 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_ctor_get(x_1, 4);
lean_inc(x_32);
x_33 = l_Lean_PHashSet_toList___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__5(x_32);
x_34 = l_List_mapTR_loop___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__9(x_33, x_20);
x_35 = l_List_format___at_Lean_Meta_instToFormatUnificationHints___spec__4(x_34);
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__12;
x_38 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_ctor_get(x_1, 5);
lean_inc(x_39);
lean_dec(x_1);
x_40 = l_Lean_PersistentHashMap_toList___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__14(x_39);
x_41 = l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__16(x_40);
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3___closed__4;
x_44 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkEqSymm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = l_Lean_Meta_mkEqSymm(x_14, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
lean_ctor_set(x_8, 0, x_17);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_8);
lean_ctor_set(x_19, 2, x_18);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
lean_ctor_set(x_8, 0, x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_8);
lean_ctor_set(x_23, 2, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_free_object(x_8);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
return x_15;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_8, 0);
lean_inc(x_29);
lean_dec(x_8);
x_30 = l_Lean_Meta_mkEqSymm(x_29, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_31);
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_1);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set(x_36, 2, x_35);
if (lean_is_scalar(x_33)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_33;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_32);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_1);
x_38 = lean_ctor_get(x_30, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_30, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_40 = x_30;
} else {
 lean_dec_ref(x_30);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkCast___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("cast", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkCast___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_mkCast___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkCast___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCast(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l_Lean_Meta_Simp_Result_getProof(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_Simp_mkCast___closed__3;
x_12 = lean_array_push(x_11, x_9);
x_13 = lean_array_push(x_12, x_2);
x_14 = l_Lean_Meta_Simp_mkCast___closed__2;
x_15 = l_Lean_Meta_mkAppM(x_14, x_13, x_3, x_4, x_5, x_6, x_10);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_getPropHyps___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_uget(x_3, x_5);
x_15 = !lean_is_exclusive(x_6);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_6, 1);
x_17 = lean_ctor_get(x_6, 0);
lean_dec(x_17);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_16);
lean_inc(x_1);
x_18 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_Simp_getPropHyps___spec__2(x_1, x_14, x_16, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_6, 0, x_22);
lean_ctor_set(x_18, 0, x_6);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_6, 0, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_6);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; 
lean_dec(x_16);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
lean_dec(x_19);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_27);
lean_ctor_set(x_6, 0, x_2);
x_28 = 1;
x_29 = lean_usize_add(x_5, x_28);
x_5 = x_29;
x_11 = x_26;
goto _start;
}
}
else
{
uint8_t x_31; 
lean_free_object(x_6);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_18);
if (x_31 == 0)
{
return x_18;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_18, 0);
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_18);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_6, 1);
lean_inc(x_35);
lean_dec(x_6);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_35);
lean_inc(x_1);
x_36 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_Simp_getPropHyps___spec__2(x_1, x_14, x_35, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_35);
if (lean_is_scalar(x_39)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_39;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_38);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; 
lean_dec(x_35);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
lean_dec(x_36);
x_44 = lean_ctor_get(x_37, 0);
lean_inc(x_44);
lean_dec(x_37);
lean_inc(x_2);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_2);
lean_ctor_set(x_45, 1, x_44);
x_46 = 1;
x_47 = lean_usize_add(x_5, x_46);
x_5 = x_47;
x_6 = x_45;
x_11 = x_43;
goto _start;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_35);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_49 = lean_ctor_get(x_36, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_36, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_51 = x_36;
} else {
 lean_dec_ref(x_36);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_getPropHyps___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_array_uget(x_2, x_4);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_15 = x_5;
} else {
 lean_dec_ref(x_5);
 x_15 = lean_box(0);
}
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_14);
x_16 = x_24;
x_17 = x_10;
goto block_23;
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_13, 0);
lean_inc(x_25);
lean_dec(x_13);
x_26 = l_Lean_LocalDecl_isAuxDecl(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_Lean_LocalDecl_type(x_25);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_28 = l_Lean_Meta_isProp(x_27, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_25);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_14);
x_16 = x_32;
x_17 = x_31;
goto block_23;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_dec(x_28);
x_34 = l_Lean_LocalDecl_fvarId(x_25);
lean_dec(x_25);
x_35 = lean_array_push(x_14, x_34);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_16 = x_36;
x_17 = x_33;
goto block_23;
}
}
else
{
uint8_t x_37; 
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_28);
if (x_37 == 0)
{
return x_28;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_28, 0);
x_39 = lean_ctor_get(x_28, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_28);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; 
lean_dec(x_25);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_14);
x_16 = x_41;
x_17 = x_10;
goto block_23;
}
}
block_23:
{
lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_1);
if (lean_is_scalar(x_15)) {
 x_19 = lean_alloc_ctor(0, 2, 0);
} else {
 x_19 = x_15;
}
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
x_20 = 1;
x_21 = lean_usize_add(x_4, x_20);
x_4 = x_21;
x_5 = x_19;
x_10 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_Simp_getPropHyps___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_Simp_getPropHyps___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
x_12 = lean_array_get_size(x_9);
x_13 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_14 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_getPropHyps___spec__3(x_1, x_10, x_9, x_13, x_14, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_box(0);
x_21 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_Simp_getPropHyps___spec__2___lambda__1(x_19, x_20, x_4, x_5, x_6, x_7, x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_15, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_24);
return x_15;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_dec(x_15);
x_26 = lean_ctor_get(x_17, 0);
lean_inc(x_26);
lean_dec(x_17);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_28 = !lean_is_exclusive(x_15);
if (x_28 == 0)
{
return x_15;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_15, 0);
x_30 = lean_ctor_get(x_15, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_15);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; 
lean_dec(x_1);
x_32 = lean_ctor_get(x_2, 0);
lean_inc(x_32);
lean_dec(x_2);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_3);
x_35 = lean_array_get_size(x_32);
x_36 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_37 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_38 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_getPropHyps___spec__4(x_33, x_32, x_36, x_37, x_34, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_32);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_box(0);
x_44 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_Simp_getPropHyps___spec__2___lambda__1(x_42, x_43, x_4, x_5, x_6, x_7, x_41);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_44;
}
else
{
uint8_t x_45; 
lean_dec(x_39);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_45 = !lean_is_exclusive(x_38);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_38, 0);
lean_dec(x_46);
x_47 = lean_ctor_get(x_40, 0);
lean_inc(x_47);
lean_dec(x_40);
lean_ctor_set(x_38, 0, x_47);
return x_38;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_38, 1);
lean_inc(x_48);
lean_dec(x_38);
x_49 = lean_ctor_get(x_40, 0);
lean_inc(x_49);
lean_dec(x_40);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_51 = !lean_is_exclusive(x_38);
if (x_51 == 0)
{
return x_38;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_38, 0);
x_53 = lean_ctor_get(x_38, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_38);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_getPropHyps___spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_array_uget(x_2, x_4);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_15 = x_5;
} else {
 lean_dec_ref(x_5);
 x_15 = lean_box(0);
}
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_14);
x_16 = x_24;
x_17 = x_10;
goto block_23;
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_13, 0);
lean_inc(x_25);
lean_dec(x_13);
x_26 = l_Lean_LocalDecl_isAuxDecl(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_Lean_LocalDecl_type(x_25);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_28 = l_Lean_Meta_isProp(x_27, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_25);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_14);
x_16 = x_32;
x_17 = x_31;
goto block_23;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_dec(x_28);
x_34 = l_Lean_LocalDecl_fvarId(x_25);
lean_dec(x_25);
x_35 = lean_array_push(x_14, x_34);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_16 = x_36;
x_17 = x_33;
goto block_23;
}
}
else
{
uint8_t x_37; 
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_28);
if (x_37 == 0)
{
return x_28;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_28, 0);
x_39 = lean_ctor_get(x_28, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_28);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; 
lean_dec(x_25);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_14);
x_16 = x_41;
x_17 = x_10;
goto block_23;
}
}
block_23:
{
lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_1);
if (lean_is_scalar(x_15)) {
 x_19 = lean_alloc_ctor(0, 2, 0);
} else {
 x_19 = x_15;
}
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
x_20 = 1;
x_21 = lean_usize_add(x_4, x_20);
x_4 = x_21;
x_5 = x_19;
x_10 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_Simp_getPropHyps___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_Simp_getPropHyps___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_9 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_Simp_getPropHyps___spec__2(x_2, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
x_22 = lean_array_get_size(x_19);
x_23 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_24 = 0;
x_25 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_getPropHyps___spec__5(x_20, x_19, x_23, x_24, x_21, x_3, x_4, x_5, x_6, x_17);
lean_dec(x_19);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_25, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
lean_ctor_set(x_25, 0, x_30);
return x_25;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_26);
x_34 = !lean_is_exclusive(x_25);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_25, 0);
lean_dec(x_35);
x_36 = lean_ctor_get(x_27, 0);
lean_inc(x_36);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_36);
return x_25;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_25, 1);
lean_inc(x_37);
lean_dec(x_25);
x_38 = lean_ctor_get(x_27, 0);
lean_inc(x_38);
lean_dec(x_27);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_25);
if (x_40 == 0)
{
return x_25;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_25, 0);
x_42 = lean_ctor_get(x_25, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_25);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_9);
if (x_44 == 0)
{
return x_9;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_9, 0);
x_46 = lean_ctor_get(x_9, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_9);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getPropHyps(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Meta_DiscrTree_Trie_getElements___rarg___closed__1;
x_9 = l_Lean_PersistentArray_forIn___at_Lean_Meta_Simp_getPropHyps___spec__1(x_7, x_8, x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_getPropHyps___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_getPropHyps___spec__3(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_getPropHyps___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_getPropHyps___spec__4(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_Simp_getPropHyps___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_Simp_getPropHyps___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_getPropHyps___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_getPropHyps___spec__5(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_Simp_getPropHyps___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentArray_forIn___at_Lean_Meta_Simp_getPropHyps___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkDischargeWrapper(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_mkDischargeWrapper(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkDischargeWrapper___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_mkDischargeWrapper(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimpContext_x27___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimpContext_x27___lambda__1(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = l_Lean_Meta_getSimpCongrTheorems___rarg(x_14, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_unsigned_to_nat(1u);
x_20 = l_Lean_Syntax_getArg(x_1, x_19);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_21 = l_Lean_Elab_Tactic_elabSimpConfig(x_20, x_2, x_9, x_10, x_11, x_12, x_13, x_14, x_18);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_unsigned_to_nat(4u);
x_25 = l_Lean_Syntax_getArg(x_1, x_24);
x_26 = l_Lean_Meta_Simp_mkSimpContext_x27___lambda__1___closed__1;
x_27 = lean_array_push(x_26, x_6);
x_28 = lean_box(0);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_30, 0, x_22);
lean_ctor_set(x_30, 1, x_27);
lean_ctor_set(x_30, 2, x_17);
lean_ctor_set(x_30, 3, x_28);
lean_ctor_set(x_30, 4, x_29);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_31 = l_Lean_Elab_Tactic_elabSimpArgs(x_25, x_30, x_3, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_23);
lean_dec(x_25);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get_uint8(x_32, sizeof(void*)*1);
if (x_33 == 0)
{
uint8_t x_34; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 0);
lean_dec(x_35);
x_36 = lean_ctor_get(x_32, 0);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_4);
lean_ctor_set(x_31, 0, x_37);
return x_31;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_dec(x_31);
x_39 = lean_ctor_get(x_32, 0);
lean_inc(x_39);
lean_dec(x_32);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_4);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
}
else
{
if (x_5 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_31, 1);
lean_inc(x_42);
lean_dec(x_31);
x_43 = lean_ctor_get(x_32, 0);
lean_inc(x_43);
lean_dec(x_32);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_45 = l_Lean_Meta_Simp_getPropHyps(x_11, x_12, x_13, x_14, x_42);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; size_t x_49; size_t x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_array_get_size(x_46);
x_49 = lean_usize_of_nat(x_48);
lean_dec(x_48);
x_50 = 0;
x_51 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpContext___spec__1(x_46, x_49, x_50, x_44, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_47);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_46);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_43);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_51, 0);
x_55 = lean_ctor_get(x_43, 1);
lean_dec(x_55);
lean_ctor_set(x_43, 1, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_43);
lean_ctor_set(x_56, 1, x_4);
lean_ctor_set(x_51, 0, x_56);
return x_51;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_57 = lean_ctor_get(x_51, 0);
x_58 = lean_ctor_get(x_43, 0);
x_59 = lean_ctor_get(x_43, 2);
x_60 = lean_ctor_get(x_43, 3);
x_61 = lean_ctor_get(x_43, 4);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_43);
x_62 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_62, 0, x_58);
lean_ctor_set(x_62, 1, x_57);
lean_ctor_set(x_62, 2, x_59);
lean_ctor_set(x_62, 3, x_60);
lean_ctor_set(x_62, 4, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_4);
lean_ctor_set(x_51, 0, x_63);
return x_51;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_64 = lean_ctor_get(x_51, 0);
x_65 = lean_ctor_get(x_51, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_51);
x_66 = lean_ctor_get(x_43, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_43, 2);
lean_inc(x_67);
x_68 = lean_ctor_get(x_43, 3);
lean_inc(x_68);
x_69 = lean_ctor_get(x_43, 4);
lean_inc(x_69);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 lean_ctor_release(x_43, 2);
 lean_ctor_release(x_43, 3);
 lean_ctor_release(x_43, 4);
 x_70 = x_43;
} else {
 lean_dec_ref(x_43);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(0, 5, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_66);
lean_ctor_set(x_71, 1, x_64);
lean_ctor_set(x_71, 2, x_67);
lean_ctor_set(x_71, 3, x_68);
lean_ctor_set(x_71, 4, x_69);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_4);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_65);
return x_73;
}
}
else
{
uint8_t x_74; 
lean_dec(x_43);
lean_dec(x_4);
x_74 = !lean_is_exclusive(x_51);
if (x_74 == 0)
{
return x_51;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_51, 0);
x_76 = lean_ctor_get(x_51, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_51);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_78 = !lean_is_exclusive(x_45);
if (x_78 == 0)
{
return x_45;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_45, 0);
x_80 = lean_ctor_get(x_45, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_45);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_82 = !lean_is_exclusive(x_31);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_31, 0);
lean_dec(x_83);
x_84 = lean_ctor_get(x_32, 0);
lean_inc(x_84);
lean_dec(x_32);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_4);
lean_ctor_set(x_31, 0, x_85);
return x_31;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_31, 1);
lean_inc(x_86);
lean_dec(x_31);
x_87 = lean_ctor_get(x_32, 0);
lean_inc(x_87);
lean_dec(x_32);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_4);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_86);
return x_89;
}
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_90 = !lean_is_exclusive(x_31);
if (x_90 == 0)
{
return x_31;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_31, 0);
x_92 = lean_ctor_get(x_31, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_31);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_94 = !lean_is_exclusive(x_21);
if (x_94 == 0)
{
return x_21;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_21, 0);
x_96 = lean_ctor_get(x_21, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_21);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = l_Lean_Meta_DiscrTree_empty(lean_box(0), x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__1;
x_2 = l_Lean_PersistentHashMap_empty___at_Lean_Meta_SimpTheorems_lemmaNames___default___spec__1;
x_3 = l_Lean_PersistentHashMap_empty___at_Lean_KeyedDeclsAttribute_ExtensionState_declNames___default___spec__1;
x_4 = l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__4;
x_5 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set(x_5, 4, x_2);
lean_ctor_set(x_5, 5, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("eq_self", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("iff_self", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__7;
x_2 = l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2(lean_object* x_1, uint8_t x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_6);
x_16 = lean_unsigned_to_nat(2u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
lean_inc(x_13);
lean_inc(x_9);
x_18 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_mkDischargeWrapper(x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(3u);
x_22 = l_Lean_Syntax_getArg(x_1, x_21);
x_23 = l_Lean_Syntax_isNone(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_5);
x_24 = l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__5;
x_25 = l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__11;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_26 = l_List_foldlM___at_Lean_Elab_Tactic_mkSimpContext___spec__2(x_24, x_25, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_20);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Meta_Simp_mkSimpContext_x27___lambda__1(x_1, x_2, x_3, x_19, x_4, x_27, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_28);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_30 = !lean_is_exclusive(x_26);
if (x_30 == 0)
{
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_26, 0);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_26);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; 
x_34 = l_Lean_Meta_Simp_mkSimpContext_x27___lambda__1(x_1, x_2, x_3, x_19, x_4, x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_20);
return x_34;
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimpContext_x27___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'dsimp' tactic does not support 'discharger' option", 51);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimpContext_x27___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_mkSimpContext_x27___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimpContext_x27___lambda__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; 
x_13 = 2;
x_14 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_beqSimpKind____x40_Lean_Elab_Tactic_Simp___hyg_814_(x_1, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = lean_apply_10(x_2, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_2);
x_17 = l_Lean_Meta_Simp_mkSimpContext_x27___lambda__3___closed__2;
x_18 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___spec__2(x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_18);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimpContext_x27___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'simp_all' tactic does not support 'discharger' option", 54);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimpContext_x27___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_mkSimpContext_x27___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimpContext_x27(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
if (x_5 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2(x_2, x_4, x_3, x_6, x_1, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_2);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_18 = lean_box(x_4);
x_19 = lean_box(x_3);
x_20 = lean_box(x_6);
lean_inc(x_1);
lean_inc(x_2);
x_21 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___boxed), 15, 5);
lean_closure_set(x_21, 0, x_2);
lean_closure_set(x_21, 1, x_18);
lean_closure_set(x_21, 2, x_19);
lean_closure_set(x_21, 3, x_20);
lean_closure_set(x_21, 4, x_1);
x_22 = lean_unsigned_to_nat(2u);
x_23 = l_Lean_Syntax_getArg(x_2, x_22);
x_24 = l_Lean_Syntax_isNone(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
uint8_t x_25; uint8_t x_26; 
lean_dec(x_2);
lean_dec(x_1);
x_25 = 1;
x_26 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_beqSimpKind____x40_Lean_Elab_Tactic_Simp___hyg_814_(x_4, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_box(0);
x_28 = l_Lean_Meta_Simp_mkSimpContext_x27___lambda__3(x_4, x_21, x_27, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_21);
x_29 = l_Lean_Meta_Simp_mkSimpContext_x27___closed__2;
x_30 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___spec__2(x_29, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
return x_30;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_30);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_21);
x_35 = lean_box(0);
x_36 = l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2(x_2, x_4, x_3, x_6, x_1, x_35, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_2);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimpContext_x27___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_16 = lean_unbox(x_2);
lean_dec(x_2);
x_17 = lean_unbox(x_3);
lean_dec(x_3);
x_18 = lean_unbox(x_5);
lean_dec(x_5);
x_19 = l_Lean_Meta_Simp_mkSimpContext_x27___lambda__1(x_1, x_16, x_17, x_4, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_16 = lean_unbox(x_2);
lean_dec(x_2);
x_17 = lean_unbox(x_3);
lean_dec(x_3);
x_18 = lean_unbox(x_4);
lean_dec(x_4);
x_19 = l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2(x_1, x_16, x_17, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimpContext_x27___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = l_Lean_Meta_Simp_mkSimpContext_x27___lambda__3(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimpContext_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_16 = lean_unbox(x_3);
lean_dec(x_3);
x_17 = lean_unbox(x_4);
lean_dec(x_4);
x_18 = lean_unbox(x_5);
lean_dec(x_5);
x_19 = lean_unbox(x_6);
lean_dec(x_6);
x_20 = l_Lean_Meta_Simp_mkSimpContext_x27(x_1, x_2, x_16, x_17, x_18, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkTypeIsProp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_shouldPreprocess___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___lambda__1___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_shouldPreprocess(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Meta_shouldPreprocess___closed__1;
x_8 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_preprocess(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go(x_3, x_4, x_1, x_2, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_preprocess___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lean_Meta_preprocess(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpTheoremCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpTheoremCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_Meta_mkSimpTheoremCore(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Meta_Simp_mkSimpTheoremsFromConst_x27___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec(x_8);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get(x_9, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_dec(x_9);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_4);
x_22 = l_Lean_Meta_mkAuxLemma(x_4, x_19, x_18, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_23);
x_25 = lean_array_push(x_20, x_23);
lean_inc(x_1);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_1);
lean_inc(x_6);
lean_inc(x_23);
x_27 = l_Lean_Expr_const___override(x_23, x_6);
lean_inc(x_5);
x_28 = l_Lean_Expr_const___override(x_23, x_5);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_3);
lean_inc(x_7);
x_29 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore(x_26, x_27, x_7, x_28, x_2, x_3, x_10, x_11, x_12, x_13, x_24);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_array_push(x_21, x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_25);
lean_ctor_set(x_33, 1, x_32);
x_8 = x_17;
x_9 = x_33;
x_14 = x_31;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec(x_25);
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_29);
if (x_35 == 0)
{
return x_29;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_29, 0);
x_37 = lean_ctor_get(x_29, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_29);
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
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_22);
if (x_39 == 0)
{
return x_22;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_22, 0);
x_41 = lean_ctor_get(x_22, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_22);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimpTheoremsFromConst_x27___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DiscrTree_Trie_getElements___rarg___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimpTheoremsFromConst_x27(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_1);
x_10 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_ConstantInfo_levelParams(x_11);
lean_dec(x_11);
x_14 = lean_box(0);
lean_inc(x_13);
x_15 = l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(x_13, x_14);
lean_inc(x_15);
lean_inc(x_1);
x_16 = l_Lean_Expr_const___override(x_1, x_15);
x_17 = !lean_is_exclusive(x_5);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_5, 0);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
uint8_t x_20; lean_object* x_21; 
x_20 = 2;
lean_ctor_set_uint8(x_18, 5, x_20);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_16);
x_21 = lean_infer_type(x_16, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_22);
x_24 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp(x_22, x_5, x_6, x_7, x_8, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_Meta_shouldPreprocess___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_22);
x_27 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_22, x_26, x_5, x_6, x_7, x_8, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
if (x_3 == 0)
{
uint8_t x_58; 
x_58 = lean_unbox(x_28);
lean_dec(x_28);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_13);
lean_inc(x_1);
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_1);
x_60 = l_Lean_Expr_const___override(x_1, x_14);
x_61 = l_Lean_Meta_DiscrTree_Trie_getElements___rarg___closed__1;
x_62 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore(x_59, x_16, x_61, x_60, x_2, x_4, x_5, x_6, x_7, x_8, x_29);
if (lean_obj_tag(x_62) == 0)
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_62, 0);
x_65 = l_Lean_Meta_Simp_mkSimpContext_x27___lambda__1___closed__1;
x_66 = lean_array_push(x_65, x_64);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_61);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set(x_62, 0, x_67);
return x_62;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_62, 0);
x_69 = lean_ctor_get(x_62, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_62);
x_70 = l_Lean_Meta_Simp_mkSimpContext_x27___lambda__1___closed__1;
x_71 = lean_array_push(x_70, x_68);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_61);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_69);
return x_73;
}
}
else
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_62);
if (x_74 == 0)
{
return x_62;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_62, 0);
x_76 = lean_ctor_get(x_62, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_62);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
lean_object* x_78; 
x_78 = lean_box(0);
x_30 = x_78;
goto block_57;
}
}
else
{
lean_object* x_79; 
lean_dec(x_28);
x_79 = lean_box(0);
x_30 = x_79;
goto block_57;
}
block_57:
{
uint8_t x_31; lean_object* x_32; 
lean_dec(x_30);
x_31 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_32 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go(x_3, x_31, x_16, x_22, x_5, x_6, x_7, x_8, x_29);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Meta_DiscrTree_Trie_getElements___rarg___closed__1;
x_36 = l_Lean_Meta_Simp_mkSimpTheoremsFromConst_x27___closed__1;
x_37 = l_List_forIn_loop___at_Lean_Meta_Simp_mkSimpTheoremsFromConst_x27___spec__1(x_1, x_2, x_4, x_13, x_14, x_15, x_35, x_33, x_36, x_5, x_6, x_7, x_8, x_34);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_37, 0, x_42);
return x_37;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_37, 0);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_37);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_44);
return x_48;
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_37);
if (x_49 == 0)
{
return x_37;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_37, 0);
x_51 = lean_ctor_get(x_37, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_37);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_5);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_32);
if (x_53 == 0)
{
return x_32;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_32, 0);
x_55 = lean_ctor_get(x_32, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_32);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_22);
lean_dec(x_5);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_27);
if (x_80 == 0)
{
return x_27;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_27, 0);
x_82 = lean_ctor_get(x_27, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_27);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_22);
lean_dec(x_5);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_24);
if (x_84 == 0)
{
return x_24;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_24, 0);
x_86 = lean_ctor_get(x_24, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_24);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_5);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_21);
if (x_88 == 0)
{
return x_21;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_21, 0);
x_90 = lean_ctor_get(x_21, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_21);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
uint8_t x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; uint8_t x_96; uint8_t x_97; uint8_t x_98; uint8_t x_99; uint8_t x_100; uint8_t x_101; uint8_t x_102; uint8_t x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; 
x_92 = lean_ctor_get_uint8(x_18, 0);
x_93 = lean_ctor_get_uint8(x_18, 1);
x_94 = lean_ctor_get_uint8(x_18, 2);
x_95 = lean_ctor_get_uint8(x_18, 3);
x_96 = lean_ctor_get_uint8(x_18, 4);
x_97 = lean_ctor_get_uint8(x_18, 6);
x_98 = lean_ctor_get_uint8(x_18, 7);
x_99 = lean_ctor_get_uint8(x_18, 8);
x_100 = lean_ctor_get_uint8(x_18, 9);
x_101 = lean_ctor_get_uint8(x_18, 10);
x_102 = lean_ctor_get_uint8(x_18, 11);
x_103 = lean_ctor_get_uint8(x_18, 12);
lean_dec(x_18);
x_104 = 2;
x_105 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_105, 0, x_92);
lean_ctor_set_uint8(x_105, 1, x_93);
lean_ctor_set_uint8(x_105, 2, x_94);
lean_ctor_set_uint8(x_105, 3, x_95);
lean_ctor_set_uint8(x_105, 4, x_96);
lean_ctor_set_uint8(x_105, 5, x_104);
lean_ctor_set_uint8(x_105, 6, x_97);
lean_ctor_set_uint8(x_105, 7, x_98);
lean_ctor_set_uint8(x_105, 8, x_99);
lean_ctor_set_uint8(x_105, 9, x_100);
lean_ctor_set_uint8(x_105, 10, x_101);
lean_ctor_set_uint8(x_105, 11, x_102);
lean_ctor_set_uint8(x_105, 12, x_103);
lean_ctor_set(x_5, 0, x_105);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_16);
x_106 = lean_infer_type(x_16, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_107);
x_109 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp(x_107, x_5, x_6, x_7, x_8, x_108);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec(x_109);
x_111 = l_Lean_Meta_shouldPreprocess___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_107);
x_112 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_107, x_111, x_5, x_6, x_7, x_8, x_110);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
if (x_3 == 0)
{
uint8_t x_139; 
x_139 = lean_unbox(x_113);
lean_dec(x_113);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_107);
lean_dec(x_15);
lean_dec(x_13);
lean_inc(x_1);
x_140 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_140, 0, x_1);
x_141 = l_Lean_Expr_const___override(x_1, x_14);
x_142 = l_Lean_Meta_DiscrTree_Trie_getElements___rarg___closed__1;
x_143 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore(x_140, x_16, x_142, x_141, x_2, x_4, x_5, x_6, x_7, x_8, x_114);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_146 = x_143;
} else {
 lean_dec_ref(x_143);
 x_146 = lean_box(0);
}
x_147 = l_Lean_Meta_Simp_mkSimpContext_x27___lambda__1___closed__1;
x_148 = lean_array_push(x_147, x_144);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_142);
lean_ctor_set(x_149, 1, x_148);
if (lean_is_scalar(x_146)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_146;
}
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_145);
return x_150;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_151 = lean_ctor_get(x_143, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_143, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_153 = x_143;
} else {
 lean_dec_ref(x_143);
 x_153 = lean_box(0);
}
if (lean_is_scalar(x_153)) {
 x_154 = lean_alloc_ctor(1, 2, 0);
} else {
 x_154 = x_153;
}
lean_ctor_set(x_154, 0, x_151);
lean_ctor_set(x_154, 1, x_152);
return x_154;
}
}
else
{
lean_object* x_155; 
x_155 = lean_box(0);
x_115 = x_155;
goto block_138;
}
}
else
{
lean_object* x_156; 
lean_dec(x_113);
x_156 = lean_box(0);
x_115 = x_156;
goto block_138;
}
block_138:
{
uint8_t x_116; lean_object* x_117; 
lean_dec(x_115);
x_116 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_117 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go(x_3, x_116, x_16, x_107, x_5, x_6, x_7, x_8, x_114);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = l_Lean_Meta_DiscrTree_Trie_getElements___rarg___closed__1;
x_121 = l_Lean_Meta_Simp_mkSimpTheoremsFromConst_x27___closed__1;
x_122 = l_List_forIn_loop___at_Lean_Meta_Simp_mkSimpTheoremsFromConst_x27___spec__1(x_1, x_2, x_4, x_13, x_14, x_15, x_120, x_118, x_121, x_5, x_6, x_7, x_8, x_119);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_125 = x_122;
} else {
 lean_dec_ref(x_122);
 x_125 = lean_box(0);
}
x_126 = lean_ctor_get(x_123, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_123, 1);
lean_inc(x_127);
lean_dec(x_123);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
if (lean_is_scalar(x_125)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_125;
}
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_124);
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_130 = lean_ctor_get(x_122, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_122, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_132 = x_122;
} else {
 lean_dec_ref(x_122);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(1, 2, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_131);
return x_133;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_5);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_134 = lean_ctor_get(x_117, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_117, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_136 = x_117;
} else {
 lean_dec_ref(x_117);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_107);
lean_dec(x_5);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_157 = lean_ctor_get(x_112, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_112, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_159 = x_112;
} else {
 lean_dec_ref(x_112);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_107);
lean_dec(x_5);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_161 = lean_ctor_get(x_109, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_109, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_163 = x_109;
} else {
 lean_dec_ref(x_109);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_5);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_165 = lean_ctor_get(x_106, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_106, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_167 = x_106;
} else {
 lean_dec_ref(x_106);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(1, 2, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_166);
return x_168;
}
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; uint8_t x_176; uint8_t x_177; uint8_t x_178; uint8_t x_179; uint8_t x_180; uint8_t x_181; uint8_t x_182; uint8_t x_183; uint8_t x_184; uint8_t x_185; uint8_t x_186; lean_object* x_187; uint8_t x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_169 = lean_ctor_get(x_5, 0);
x_170 = lean_ctor_get(x_5, 1);
x_171 = lean_ctor_get(x_5, 2);
x_172 = lean_ctor_get(x_5, 3);
x_173 = lean_ctor_get(x_5, 4);
x_174 = lean_ctor_get(x_5, 5);
lean_inc(x_174);
lean_inc(x_173);
lean_inc(x_172);
lean_inc(x_171);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_5);
x_175 = lean_ctor_get_uint8(x_169, 0);
x_176 = lean_ctor_get_uint8(x_169, 1);
x_177 = lean_ctor_get_uint8(x_169, 2);
x_178 = lean_ctor_get_uint8(x_169, 3);
x_179 = lean_ctor_get_uint8(x_169, 4);
x_180 = lean_ctor_get_uint8(x_169, 6);
x_181 = lean_ctor_get_uint8(x_169, 7);
x_182 = lean_ctor_get_uint8(x_169, 8);
x_183 = lean_ctor_get_uint8(x_169, 9);
x_184 = lean_ctor_get_uint8(x_169, 10);
x_185 = lean_ctor_get_uint8(x_169, 11);
x_186 = lean_ctor_get_uint8(x_169, 12);
if (lean_is_exclusive(x_169)) {
 x_187 = x_169;
} else {
 lean_dec_ref(x_169);
 x_187 = lean_box(0);
}
x_188 = 2;
if (lean_is_scalar(x_187)) {
 x_189 = lean_alloc_ctor(0, 0, 13);
} else {
 x_189 = x_187;
}
lean_ctor_set_uint8(x_189, 0, x_175);
lean_ctor_set_uint8(x_189, 1, x_176);
lean_ctor_set_uint8(x_189, 2, x_177);
lean_ctor_set_uint8(x_189, 3, x_178);
lean_ctor_set_uint8(x_189, 4, x_179);
lean_ctor_set_uint8(x_189, 5, x_188);
lean_ctor_set_uint8(x_189, 6, x_180);
lean_ctor_set_uint8(x_189, 7, x_181);
lean_ctor_set_uint8(x_189, 8, x_182);
lean_ctor_set_uint8(x_189, 9, x_183);
lean_ctor_set_uint8(x_189, 10, x_184);
lean_ctor_set_uint8(x_189, 11, x_185);
lean_ctor_set_uint8(x_189, 12, x_186);
x_190 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_170);
lean_ctor_set(x_190, 2, x_171);
lean_ctor_set(x_190, 3, x_172);
lean_ctor_set(x_190, 4, x_173);
lean_ctor_set(x_190, 5, x_174);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_190);
lean_inc(x_16);
x_191 = lean_infer_type(x_16, x_190, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec(x_191);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_190);
lean_inc(x_192);
x_194 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp(x_192, x_190, x_6, x_7, x_8, x_193);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_194, 1);
lean_inc(x_195);
lean_dec(x_194);
x_196 = l_Lean_Meta_shouldPreprocess___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_190);
lean_inc(x_192);
x_197 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_192, x_196, x_190, x_6, x_7, x_8, x_195);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
lean_dec(x_197);
if (x_3 == 0)
{
uint8_t x_224; 
x_224 = lean_unbox(x_198);
lean_dec(x_198);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_192);
lean_dec(x_15);
lean_dec(x_13);
lean_inc(x_1);
x_225 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_225, 0, x_1);
x_226 = l_Lean_Expr_const___override(x_1, x_14);
x_227 = l_Lean_Meta_DiscrTree_Trie_getElements___rarg___closed__1;
x_228 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore(x_225, x_16, x_227, x_226, x_2, x_4, x_190, x_6, x_7, x_8, x_199);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_231 = x_228;
} else {
 lean_dec_ref(x_228);
 x_231 = lean_box(0);
}
x_232 = l_Lean_Meta_Simp_mkSimpContext_x27___lambda__1___closed__1;
x_233 = lean_array_push(x_232, x_229);
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_227);
lean_ctor_set(x_234, 1, x_233);
if (lean_is_scalar(x_231)) {
 x_235 = lean_alloc_ctor(0, 2, 0);
} else {
 x_235 = x_231;
}
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_230);
return x_235;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_236 = lean_ctor_get(x_228, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_228, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_238 = x_228;
} else {
 lean_dec_ref(x_228);
 x_238 = lean_box(0);
}
if (lean_is_scalar(x_238)) {
 x_239 = lean_alloc_ctor(1, 2, 0);
} else {
 x_239 = x_238;
}
lean_ctor_set(x_239, 0, x_236);
lean_ctor_set(x_239, 1, x_237);
return x_239;
}
}
else
{
lean_object* x_240; 
x_240 = lean_box(0);
x_200 = x_240;
goto block_223;
}
}
else
{
lean_object* x_241; 
lean_dec(x_198);
x_241 = lean_box(0);
x_200 = x_241;
goto block_223;
}
block_223:
{
uint8_t x_201; lean_object* x_202; 
lean_dec(x_200);
x_201 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_190);
x_202 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go(x_3, x_201, x_16, x_192, x_190, x_6, x_7, x_8, x_199);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
lean_dec(x_202);
x_205 = l_Lean_Meta_DiscrTree_Trie_getElements___rarg___closed__1;
x_206 = l_Lean_Meta_Simp_mkSimpTheoremsFromConst_x27___closed__1;
x_207 = l_List_forIn_loop___at_Lean_Meta_Simp_mkSimpTheoremsFromConst_x27___spec__1(x_1, x_2, x_4, x_13, x_14, x_15, x_205, x_203, x_206, x_190, x_6, x_7, x_8, x_204);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_210 = x_207;
} else {
 lean_dec_ref(x_207);
 x_210 = lean_box(0);
}
x_211 = lean_ctor_get(x_208, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_208, 1);
lean_inc(x_212);
lean_dec(x_208);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
if (lean_is_scalar(x_210)) {
 x_214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_214 = x_210;
}
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_209);
return x_214;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_215 = lean_ctor_get(x_207, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_207, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_217 = x_207;
} else {
 lean_dec_ref(x_207);
 x_217 = lean_box(0);
}
if (lean_is_scalar(x_217)) {
 x_218 = lean_alloc_ctor(1, 2, 0);
} else {
 x_218 = x_217;
}
lean_ctor_set(x_218, 0, x_215);
lean_ctor_set(x_218, 1, x_216);
return x_218;
}
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
lean_dec(x_190);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_219 = lean_ctor_get(x_202, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_202, 1);
lean_inc(x_220);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_221 = x_202;
} else {
 lean_dec_ref(x_202);
 x_221 = lean_box(0);
}
if (lean_is_scalar(x_221)) {
 x_222 = lean_alloc_ctor(1, 2, 0);
} else {
 x_222 = x_221;
}
lean_ctor_set(x_222, 0, x_219);
lean_ctor_set(x_222, 1, x_220);
return x_222;
}
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_192);
lean_dec(x_190);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_242 = lean_ctor_get(x_197, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_197, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_244 = x_197;
} else {
 lean_dec_ref(x_197);
 x_244 = lean_box(0);
}
if (lean_is_scalar(x_244)) {
 x_245 = lean_alloc_ctor(1, 2, 0);
} else {
 x_245 = x_244;
}
lean_ctor_set(x_245, 0, x_242);
lean_ctor_set(x_245, 1, x_243);
return x_245;
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_192);
lean_dec(x_190);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_246 = lean_ctor_get(x_194, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_194, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_248 = x_194;
} else {
 lean_dec_ref(x_194);
 x_248 = lean_box(0);
}
if (lean_is_scalar(x_248)) {
 x_249 = lean_alloc_ctor(1, 2, 0);
} else {
 x_249 = x_248;
}
lean_ctor_set(x_249, 0, x_246);
lean_ctor_set(x_249, 1, x_247);
return x_249;
}
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_190);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_250 = lean_ctor_get(x_191, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_191, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_252 = x_191;
} else {
 lean_dec_ref(x_191);
 x_252 = lean_box(0);
}
if (lean_is_scalar(x_252)) {
 x_253 = lean_alloc_ctor(1, 2, 0);
} else {
 x_253 = x_252;
}
lean_ctor_set(x_253, 0, x_250);
lean_ctor_set(x_253, 1, x_251);
return x_253;
}
}
}
else
{
uint8_t x_254; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_254 = !lean_is_exclusive(x_10);
if (x_254 == 0)
{
return x_10;
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_255 = lean_ctor_get(x_10, 0);
x_256 = lean_ctor_get(x_10, 1);
lean_inc(x_256);
lean_inc(x_255);
lean_dec(x_10);
x_257 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_257, 0, x_255);
lean_ctor_set(x_257, 1, x_256);
return x_257;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Meta_Simp_mkSimpTheoremsFromConst_x27___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_2);
lean_dec(x_2);
x_16 = l_List_forIn_loop___at_Lean_Meta_Simp_mkSimpTheoremsFromConst_x27___spec__1(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimpTheoremsFromConst_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Lean_Meta_Simp_mkSimpTheoremsFromConst_x27(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_addSimpTheorem_x27___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
lean_dec(x_6);
x_14 = lean_array_uget(x_3, x_5);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_inc(x_9);
lean_inc(x_1);
x_16 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpTheorem___spec__1(x_1, x_15, x_2, x_7, x_8, x_9, x_10, x_11);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = 1;
x_19 = lean_usize_add(x_5, x_18);
x_20 = lean_box(0);
x_5 = x_19;
x_6 = x_20;
x_11 = x_17;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimpTheorem_x27(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_12 = l_Lean_Meta_Simp_mkSimpTheoremsFromConst_x27(x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_array_get_size(x_16);
x_18 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_19 = 0;
x_20 = lean_box(0);
x_21 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_addSimpTheorem_x27___spec__1(x_1, x_5, x_16, x_18, x_19, x_20, x_7, x_8, x_9, x_10, x_14);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_16);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_15);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_12);
if (x_26 == 0)
{
return x_12;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_12, 0);
x_28 = lean_ctor_get(x_12, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_12);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_addSimpTheorem_x27___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_addSimpTheorem_x27___spec__1(x_1, x_12, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimpTheorem_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l_Lean_Meta_Simp_addSimpTheorem_x27(x_1, x_2, x_12, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Simp_addSimpAttr___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_addSimpAttr___spec__2(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_7, x_6);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_array_uget(x_5, x_7);
x_17 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
lean_inc(x_1);
x_18 = l_Lean_Meta_Simp_addSimpTheorem_x27(x_1, x_16, x_3, x_17, x_2, x_4, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Array_append___rarg(x_8, x_19);
x_22 = 1;
x_23 = lean_usize_add(x_7, x_22);
x_7 = x_23;
x_8 = x_21;
x_13 = x_20;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_18);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_addSimpAttr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid 'simp', it is not a proposition nor a definition (to unfold)", 68);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_addSimpAttr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_addSimpAttr___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimpAttr(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_1);
x_11 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_ConstantInfo_type(x_12);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_15 = l_Lean_Meta_isProp(x_14, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = l_Lean_ConstantInfo_hasValue(x_12);
lean_dec(x_12);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_20 = l_Lean_Meta_Simp_addSimpAttr___closed__2;
x_21 = l_Lean_throwError___at_Lean_Meta_Simp_addSimpAttr___spec__1(x_20, x_6, x_7, x_8, x_9, x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_21;
}
else
{
uint8_t x_22; lean_object* x_23; 
x_22 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_23 = l_Lean_Meta_getEqnsFor_x3f(x_1, x_22, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_5);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_1);
x_27 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1(x_2, x_26, x_3, x_6, x_7, x_8, x_9, x_25);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = l_Lean_Meta_DiscrTree_Trie_getElements___rarg___closed__1;
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = l_Lean_Meta_DiscrTree_Trie_getElements___rarg___closed__1;
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; size_t x_37; size_t x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_23, 1);
lean_inc(x_34);
lean_dec(x_23);
x_35 = lean_ctor_get(x_24, 0);
lean_inc(x_35);
lean_dec(x_24);
x_36 = lean_array_get_size(x_35);
x_37 = lean_usize_of_nat(x_36);
lean_dec(x_36);
x_38 = 0;
x_39 = l_Lean_Meta_DiscrTree_Trie_getElements___rarg___closed__1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
x_40 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_addSimpAttr___spec__2(x_2, x_3, x_4, x_5, x_35, x_37, x_38, x_39, x_6, x_7, x_8, x_9, x_34);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
lean_inc(x_1);
x_43 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_35);
lean_inc(x_8);
lean_inc(x_2);
x_44 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1(x_2, x_43, x_3, x_6, x_7, x_8, x_9, x_42);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_st_ref_get(x_9, x_45);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = lean_ctor_get(x_46, 1);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_1);
x_51 = l_Lean_Meta_hasSmartUnfoldingDecl(x_50, x_1);
if (x_51 == 0)
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set(x_46, 0, x_41);
return x_46;
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
lean_free_object(x_46);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_1);
x_53 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1(x_2, x_52, x_3, x_6, x_7, x_8, x_9, x_49);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 0);
lean_dec(x_55);
lean_ctor_set(x_53, 0, x_41);
return x_53;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_41);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_58 = lean_ctor_get(x_46, 0);
x_59 = lean_ctor_get(x_46, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_46);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
lean_dec(x_58);
lean_inc(x_1);
x_61 = l_Lean_Meta_hasSmartUnfoldingDecl(x_60, x_1);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_41);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_1);
x_64 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_mkSimpAttr___spec__1(x_2, x_63, x_3, x_6, x_7, x_8, x_9, x_59);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
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
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_41);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_35);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_40);
if (x_68 == 0)
{
return x_40;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_40, 0);
x_70 = lean_ctor_get(x_40, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_40);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_23);
if (x_72 == 0)
{
return x_23;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_23, 0);
x_74 = lean_ctor_get(x_23, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_23);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
else
{
lean_object* x_76; uint8_t x_77; lean_object* x_78; 
lean_dec(x_12);
x_76 = lean_ctor_get(x_15, 1);
lean_inc(x_76);
lean_dec(x_15);
x_77 = 0;
x_78 = l_Lean_Meta_Simp_addSimpTheorem_x27(x_2, x_1, x_4, x_77, x_3, x_5, x_6, x_7, x_8, x_9, x_76);
return x_78;
}
}
else
{
uint8_t x_79; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_15);
if (x_79 == 0)
{
return x_15;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_15, 0);
x_81 = lean_ctor_get(x_15, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_15);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_11);
if (x_83 == 0)
{
return x_11;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_11, 0);
x_85 = lean_ctor_get(x_11, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_11);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Simp_addSimpAttr___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_Simp_addSimpAttr___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_addSimpAttr___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox(x_3);
lean_dec(x_3);
x_16 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_17 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_18 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_addSimpAttr___spec__2(x_1, x_14, x_15, x_4, x_5, x_16, x_17, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimpAttr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Lean_Meta_Simp_addSimpAttr(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
static lean_object* _init_l_Lean_Meta_Simp_addSimpAttrFromSyntax___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_addSimpAttrFromSyntax___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Parser", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_addSimpAttrFromSyntax___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Tactic", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_addSimpAttrFromSyntax___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("simpPost", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_addSimpAttrFromSyntax___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_addSimpAttrFromSyntax___closed__1;
x_2 = l_Lean_Meta_Simp_addSimpAttrFromSyntax___closed__2;
x_3 = l_Lean_Meta_Simp_addSimpAttrFromSyntax___closed__3;
x_4 = l_Lean_Meta_Simp_addSimpAttrFromSyntax___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimpAttrFromSyntax(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_4, x_10);
x_12 = l_Lean_Syntax_isNone(x_11);
x_13 = lean_unsigned_to_nat(2u);
x_14 = l_Lean_Syntax_getArg(x_4, x_13);
lean_inc(x_8);
lean_inc(x_7);
x_15 = l_Lean_getAttrParamOptPrio(x_14, x_7, x_8, x_9);
if (x_12 == 0)
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Syntax_getArg(x_11, x_18);
lean_dec(x_11);
x_20 = l_Lean_Syntax_getKind(x_19);
x_21 = l_Lean_Meta_Simp_addSimpAttrFromSyntax___closed__5;
x_22 = lean_name_eq(x_20, x_21);
lean_dec(x_20);
x_23 = l_Lean_Meta_Simp_addSimpAttr(x_1, x_2, x_3, x_22, x_16, x_5, x_6, x_7, x_8, x_17);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
return x_15;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_15);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_dec(x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_15, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_dec(x_15);
x_30 = 1;
x_31 = l_Lean_Meta_Simp_addSimpAttr(x_1, x_2, x_3, x_30, x_28, x_5, x_6, x_7, x_8, x_29);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_15);
if (x_32 == 0)
{
return x_15;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_15, 0);
x_34 = lean_ctor_get(x_15, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_15);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimpAttrFromSyntax___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Meta_Simp_addSimpAttrFromSyntax(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_simpTheoremsOfNames___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec(x_2);
x_11 = 1;
x_12 = 0;
x_13 = lean_unsigned_to_nat(1000u);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_14 = l_Lean_Meta_SimpTheorems_addConst(x_1, x_9, x_11, x_12, x_13, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_1 = x_15;
x_2 = x_10;
x_7 = x_16;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_simpTheoremsOfNames___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_simpExtension;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpTheoremsOfNames(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__5;
x_9 = l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__11;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_10 = l_List_foldlM___at_Lean_Meta_simpTheoremsOfNames___spec__1(x_8, x_9, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_simpTheoremsOfNames___closed__1;
x_14 = l_Lean_Meta_SimpExtension_getTheorems(x_13, x_5, x_6, x_12);
if (x_2 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_11);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_List_foldlM___at_Lean_Meta_simpTheoremsOfNames___spec__1(x_15, x_1, x_3, x_4, x_5, x_6, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = l_List_foldlM___at_Lean_Meta_simpTheoremsOfNames___spec__1(x_11, x_1, x_3, x_4, x_5, x_6, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
return x_10;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_10);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpTheoremsOfNames___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Meta_simpTheoremsOfNames(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_ofNames(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
x_9 = l_Lean_Meta_simpTheoremsOfNames(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_getSimpCongrTheorems___rarg(x_7, x_11);
lean_dec(x_7);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l_Lean_Meta_Simp_mkSimpContext_x27___lambda__1___closed__1;
x_16 = lean_array_push(x_15, x_10);
x_17 = lean_box(0);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_19, 0, x_3);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_14);
lean_ctor_set(x_19, 3, x_17);
lean_ctor_set(x_19, 4, x_18);
lean_ctor_set(x_12, 0, x_19);
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = l_Lean_Meta_Simp_mkSimpContext_x27___lambda__1___closed__1;
x_23 = lean_array_push(x_22, x_10);
x_24 = lean_box(0);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_26, 0, x_3);
lean_ctor_set(x_26, 1, x_23);
lean_ctor_set(x_26, 2, x_20);
lean_ctor_set(x_26, 3, x_24);
lean_ctor_set(x_26, 4, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_21);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_7);
lean_dec(x_3);
x_28 = !lean_is_exclusive(x_9);
if (x_28 == 0)
{
return x_9;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_9, 0);
x_30 = lean_ctor_get(x_9, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_9);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_ofNames___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_Simp_Context_ofNames(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_simpOnlyNames___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpOnlyNames(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = 1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_10 = l_Lean_Meta_Simp_Context_ofNames(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = l_Lean_Meta_simpOnlyNames___closed__1;
x_15 = l_Lean_Meta_simp(x_2, x_11, x_13, x_14, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_15);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_10);
if (x_27 == 0)
{
return x_10;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_10, 0);
x_29 = lean_ctor_get(x_10, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_10);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_8 = lean_infer_type(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = lean_apply_6(x_1, x_9, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Lean_Meta_mkExpectedTypeHint(x_2, x_15, x_3, x_4, x_5, x_6, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_ctor_get(x_12, 0);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
lean_dec(x_13);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_20 = l_Lean_Meta_mkEqMP(x_19, x_2, x_3, x_4, x_5, x_6, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Meta_mkExpectedTypeHint(x_21, x_18, x_3, x_4, x_5, x_6, x_22);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_11);
if (x_28 == 0)
{
return x_11;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_11, 0);
x_30 = lean_ctor_get(x_11, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_11);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_8);
if (x_32 == 0)
{
return x_8;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_8, 0);
x_34 = lean_ctor_get(x_8, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_8);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
static lean_object* _init_l_Lean_Meta_simpEq___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Eq", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_simpEq___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_simpEq___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpEq___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_Meta_simpEq___lambda__1___closed__2;
x_16 = l_Lean_Expr_const___override(x_15, x_14);
x_17 = l_Lean_mkApp3(x_16, x_2, x_3, x_4);
x_18 = 0;
x_19 = 1;
x_20 = 1;
lean_inc(x_5);
x_21 = l_Lean_Meta_mkForallFVars(x_5, x_17, x_18, x_19, x_20, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Meta_mkLambdaFVars(x_5, x_6, x_18, x_19, x_20, x_8, x_9, x_10, x_11, x_23);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_24, 0);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_24);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_22);
lean_ctor_set(x_30, 1, x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_22);
x_32 = !lean_is_exclusive(x_24);
if (x_32 == 0)
{
return x_24;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_24, 0);
x_34 = lean_ctor_get(x_24, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_24);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_6);
lean_dec(x_5);
x_36 = !lean_is_exclusive(x_21);
if (x_36 == 0)
{
return x_21;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_21, 0);
x_38 = lean_ctor_get(x_21, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_21);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpEq___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_dec(x_8);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = l_Lean_Meta_simpEq___lambda__1(x_1, x_2, x_3, x_4, x_5, x_7, x_14, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_6, 0);
lean_inc(x_16);
lean_dec(x_6);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_17 = l_Lean_Meta_mkEqTrans(x_7, x_16, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_box(0);
x_21 = l_Lean_Meta_simpEq___lambda__1(x_1, x_2, x_3, x_4, x_5, x_18, x_20, x_9, x_10, x_11, x_12, x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
static lean_object* _init_l_Lean_Meta_simpEq___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("simpEq expecting Eq", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_simpEq___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_simpEq___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpEq___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_4) == 5)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 5)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 5)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 4)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 1)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_dec(x_4);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = l_Lean_Meta_simpEq___lambda__1___closed__1;
x_21 = lean_string_dec_eq(x_19, x_20);
lean_dec(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = l_Lean_Meta_simpEq___lambda__3___closed__2;
x_23 = l_Lean_throwError___at_Lean_Elab_Term_mkCalcTrans___spec__2(x_22, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_23;
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = l_Lean_Meta_simpEq___lambda__3___closed__2;
x_25 = l_Lean_throwError___at_Lean_Elab_Term_mkCalcTrans___spec__2(x_24, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_25;
}
else
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
lean_dec(x_18);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_28 = lean_apply_6(x_1, x_16, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_33 = lean_apply_6(x_1, x_15, x_5, x_6, x_7, x_8, x_30);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
lean_inc(x_3);
x_38 = l_Lean_mkAppN(x_2, x_3);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_box(0);
x_40 = l_Lean_Meta_simpEq___lambda__2(x_27, x_17, x_31, x_36, x_3, x_37, x_38, x_39, x_5, x_6, x_7, x_8, x_35);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_32, 0);
lean_inc(x_41);
lean_dec(x_32);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_42 = l_Lean_Meta_mkEqSymm(x_41, x_5, x_6, x_7, x_8, x_35);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_45 = l_Lean_Meta_mkEqTrans(x_43, x_38, x_5, x_6, x_7, x_8, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_box(0);
x_49 = l_Lean_Meta_simpEq___lambda__2(x_27, x_17, x_31, x_36, x_3, x_37, x_46, x_48, x_5, x_6, x_7, x_8, x_47);
return x_49;
}
else
{
uint8_t x_50; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_31);
lean_dec(x_27);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_50 = !lean_is_exclusive(x_45);
if (x_50 == 0)
{
return x_45;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_45, 0);
x_52 = lean_ctor_get(x_45, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_45);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_31);
lean_dec(x_27);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_54 = !lean_is_exclusive(x_42);
if (x_54 == 0)
{
return x_42;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_42, 0);
x_56 = lean_ctor_get(x_42, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_42);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_27);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_33);
if (x_58 == 0)
{
return x_33;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_33, 0);
x_60 = lean_ctor_get(x_33, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_33);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_27);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_28);
if (x_62 == 0)
{
return x_28;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_28, 0);
x_64 = lean_ctor_get(x_28, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_28);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_26);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_66 = l_Lean_Meta_simpEq___lambda__3___closed__2;
x_67 = l_Lean_throwError___at_Lean_Elab_Term_mkCalcTrans___spec__2(x_66, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_67;
}
}
}
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_68 = l_Lean_Meta_simpEq___lambda__3___closed__2;
x_69 = l_Lean_throwError___at_Lean_Elab_Term_mkCalcTrans___spec__2(x_68, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_70 = l_Lean_Meta_simpEq___lambda__3___closed__2;
x_71 = l_Lean_throwError___at_Lean_Elab_Term_mkCalcTrans___spec__2(x_70, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_72 = l_Lean_Meta_simpEq___lambda__3___closed__2;
x_73 = l_Lean_throwError___at_Lean_Elab_Term_mkCalcTrans___spec__2(x_72, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_74 = l_Lean_Meta_simpEq___lambda__3___closed__2;
x_75 = l_Lean_throwError___at_Lean_Elab_Term_mkCalcTrans___spec__2(x_74, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_76 = l_Lean_Meta_simpEq___lambda__3___closed__2;
x_77 = l_Lean_throwError___at_Lean_Elab_Term_mkCalcTrans___spec__2(x_76, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_78 = l_Lean_Meta_simpEq___lambda__3___closed__2;
x_79 = l_Lean_throwError___at_Lean_Elab_Term_mkCalcTrans___spec__2(x_78, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_79;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_simpEq___lambda__3), 9, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_3);
x_10 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__2___rarg(x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpEq___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_simpEq___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_13;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SimpTheorems_contains(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
lean_inc(x_1);
x_4 = l_Lean_Meta_SimpTheorems_isLemma(x_1, x_3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = l_Lean_Meta_SimpTheorems_isDeclToUnfold(x_1, x_2);
return x_5;
}
else
{
uint8_t x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = 1;
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_contains___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_SimpTheorems_contains(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInSimpSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Meta_getSimpExtension_x3f(x_1, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_2);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = 0;
x_11 = lean_box(x_10);
lean_ctor_set(x_6, 0, x_11);
return x_6;
}
else
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_dec(x_6);
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_dec(x_6);
x_17 = lean_ctor_get(x_7, 0);
lean_inc(x_17);
lean_dec(x_7);
x_18 = l_Lean_Meta_SimpExtension_getTheorems(x_17, x_3, x_4, x_16);
lean_dec(x_17);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = l_Lean_Meta_SimpTheorems_contains(x_20, x_2);
x_22 = lean_box(x_21);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_18);
x_25 = l_Lean_Meta_SimpTheorems_contains(x_23, x_2);
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInSimpSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_isInSimpSet(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_filterMap___at_Lean_Meta_getAllSimpDecls___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 0);
lean_dec(x_6);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = l_List_filterMap___at_Lean_Meta_getAllSimpDecls___spec__1(x_5);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_7);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = l_List_filterMap___at_Lean_Meta_getAllSimpDecls___spec__1(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
lean_object* x_13; 
lean_dec(x_3);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_1 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getAllSimpDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Meta_getSimpExtension_x3f(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = lean_box(0);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_dec(x_5);
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
lean_dec(x_6);
x_15 = l_Lean_Meta_SimpExtension_getTheorems(x_14, x_2, x_3, x_13);
lean_dec(x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_17, 3);
lean_inc(x_18);
x_19 = l_Lean_PHashSet_toList___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__10(x_18);
x_20 = lean_ctor_get(x_17, 2);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l_Lean_PHashSet_toList___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__5(x_20);
x_22 = l_List_filterMap___at_Lean_Meta_getAllSimpDecls___spec__1(x_21);
x_23 = l_List_appendTR___rarg(x_19, x_22);
lean_ctor_set(x_15, 0, x_23);
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_15);
x_26 = lean_ctor_get(x_24, 3);
lean_inc(x_26);
x_27 = l_Lean_PHashSet_toList___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__10(x_26);
x_28 = lean_ctor_get(x_24, 2);
lean_inc(x_28);
lean_dec(x_24);
x_29 = l_Lean_PHashSet_toList___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__5(x_28);
x_30 = l_List_filterMap___at_Lean_Meta_getAllSimpDecls___spec__1(x_29);
x_31 = l_List_appendTR___rarg(x_27, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_25);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getAllSimpDecls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_getAllSimpDecls(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Meta_getAllSimpAttrs___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_inc(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_1);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_getAllSimpAttrs___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_AssocList_foldlM___at_Lean_Meta_getAllSimpAttrs___spec__2(x_4, x_6);
lean_dec(x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashMap_toList___at_Lean_Meta_getAllSimpAttrs___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_box(0);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_4, x_4);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_getAllSimpAttrs___spec__3(x_3, x_8, x_9, x_2);
lean_dec(x_3);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Meta_getAllSimpAttrs___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = l_Lean_Meta_SimpExtension_getTheorems(x_11, x_4, x_5, x_6);
lean_dec(x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_1);
x_15 = l_Lean_Meta_SimpTheorems_contains(x_13, x_1);
if (x_15 == 0)
{
lean_dec(x_10);
x_2 = x_9;
x_6 = x_14;
goto _start;
}
else
{
lean_object* x_17; 
x_17 = lean_array_push(x_3, x_10);
x_2 = x_9;
x_3 = x_17;
x_6 = x_14;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Meta_getAllSimpAttrs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_simpExtensionMapRef;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getAllSimpAttrs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_5 = l_Lean_Meta_getAllSimpAttrs___closed__1;
x_6 = lean_st_ref_get(x_5, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_HashMap_toList___at_Lean_Meta_getAllSimpAttrs___spec__1(x_7);
x_10 = l_Lean_Meta_DiscrTree_Trie_getElements___rarg___closed__1;
x_11 = l_List_forIn_loop___at_Lean_Meta_getAllSimpAttrs___spec__4(x_1, x_9, x_10, x_2, x_3, x_8);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Meta_getAllSimpAttrs___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_AssocList_foldlM___at_Lean_Meta_getAllSimpAttrs___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_getAllSimpAttrs___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_getAllSimpAttrs___spec__3(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Meta_getAllSimpAttrs___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_forIn_loop___at_Lean_Meta_getAllSimpAttrs___spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getAllSimpAttrs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_getAllSimpAttrs(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_OpenPrivate(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Mathlib_Lean_Meta_Simp(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_OpenPrivate(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_DiscrTree_Trie_getElements___rarg___closed__1 = _init_l_Lean_Meta_DiscrTree_Trie_getElements___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_DiscrTree_Trie_getElements___rarg___closed__1);
l_Lean_PersistentHashMap_toList___at_Lean_Meta_DiscrTree_getElements___spec__1___rarg___closed__1 = _init_l_Lean_PersistentHashMap_toList___at_Lean_Meta_DiscrTree_getElements___spec__1___rarg___closed__1();
lean_mark_persistent(l_Lean_PersistentHashMap_toList___at_Lean_Meta_DiscrTree_getElements___spec__1___rarg___closed__1);
l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3___closed__1 = _init_l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3___closed__1();
lean_mark_persistent(l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3___closed__1);
l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3___closed__2 = _init_l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3___closed__2();
lean_mark_persistent(l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3___closed__2);
l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3___closed__3 = _init_l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3___closed__3();
lean_mark_persistent(l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3___closed__3);
l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3___closed__4 = _init_l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3___closed__4();
lean_mark_persistent(l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3___closed__4);
l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3___closed__5 = _init_l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3___closed__5();
lean_mark_persistent(l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3___closed__5);
l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3___closed__6 = _init_l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3___closed__6();
lean_mark_persistent(l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__3___closed__6);
l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__1 = _init_l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__1();
lean_mark_persistent(l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__1);
l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__2 = _init_l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__2();
lean_mark_persistent(l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__2);
l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__3 = _init_l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__3();
lean_mark_persistent(l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__3);
l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__4 = _init_l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__4();
lean_mark_persistent(l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__4);
l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__5 = _init_l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__5();
lean_mark_persistent(l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__5);
l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__6 = _init_l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__6();
lean_mark_persistent(l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__6);
l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__7 = _init_l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__7();
lean_mark_persistent(l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__7);
l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__8 = _init_l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__8();
lean_mark_persistent(l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__8);
l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__9 = _init_l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__9();
lean_mark_persistent(l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__9);
l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__10 = _init_l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__10();
lean_mark_persistent(l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__10);
l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__11 = _init_l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__11();
lean_mark_persistent(l_List_format___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__1___closed__11);
l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__1 = _init_l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__1();
lean_mark_persistent(l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__1);
l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__2 = _init_l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__2();
lean_mark_persistent(l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__2);
l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__3 = _init_l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__3();
lean_mark_persistent(l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__3);
l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__4 = _init_l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__4();
lean_mark_persistent(l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__4);
l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__5 = _init_l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__5();
lean_mark_persistent(l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__5);
l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__6 = _init_l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__6();
lean_mark_persistent(l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__6);
l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__7 = _init_l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__7();
lean_mark_persistent(l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__7);
l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__8 = _init_l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__8();
lean_mark_persistent(l_List_foldl___at_Lean_Meta_Simp_instToFormatSimpTheorems___spec__18___closed__8);
l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__1 = _init_l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__1);
l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__2 = _init_l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__2);
l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__3 = _init_l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__3);
l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__4 = _init_l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__4);
l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__5 = _init_l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__5);
l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__6 = _init_l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__6();
lean_mark_persistent(l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__6);
l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__7 = _init_l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__7();
lean_mark_persistent(l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__7);
l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__8 = _init_l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__8();
lean_mark_persistent(l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__8);
l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__9 = _init_l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__9();
lean_mark_persistent(l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__9);
l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__10 = _init_l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__10();
lean_mark_persistent(l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__10);
l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__11 = _init_l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__11();
lean_mark_persistent(l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__11);
l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__12 = _init_l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__12();
lean_mark_persistent(l_Lean_Meta_Simp_instToFormatSimpTheorems___closed__12);
l_Lean_Meta_Simp_mkCast___closed__1 = _init_l_Lean_Meta_Simp_mkCast___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_mkCast___closed__1);
l_Lean_Meta_Simp_mkCast___closed__2 = _init_l_Lean_Meta_Simp_mkCast___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_mkCast___closed__2);
l_Lean_Meta_Simp_mkCast___closed__3 = _init_l_Lean_Meta_Simp_mkCast___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_mkCast___closed__3);
l_Lean_Meta_Simp_mkSimpContext_x27___lambda__1___closed__1 = _init_l_Lean_Meta_Simp_mkSimpContext_x27___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_mkSimpContext_x27___lambda__1___closed__1);
l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__1 = _init_l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__1);
l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__2 = _init_l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__2);
l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__3 = _init_l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__3);
l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__4 = _init_l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__4);
l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__5 = _init_l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__5);
l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__6 = _init_l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__6);
l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__7 = _init_l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__7();
lean_mark_persistent(l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__7);
l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__8 = _init_l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__8();
lean_mark_persistent(l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__8);
l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__9 = _init_l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__9();
lean_mark_persistent(l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__9);
l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__10 = _init_l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__10();
lean_mark_persistent(l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__10);
l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__11 = _init_l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__11();
lean_mark_persistent(l_Lean_Meta_Simp_mkSimpContext_x27___lambda__2___closed__11);
l_Lean_Meta_Simp_mkSimpContext_x27___lambda__3___closed__1 = _init_l_Lean_Meta_Simp_mkSimpContext_x27___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_mkSimpContext_x27___lambda__3___closed__1);
l_Lean_Meta_Simp_mkSimpContext_x27___lambda__3___closed__2 = _init_l_Lean_Meta_Simp_mkSimpContext_x27___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_mkSimpContext_x27___lambda__3___closed__2);
l_Lean_Meta_Simp_mkSimpContext_x27___closed__1 = _init_l_Lean_Meta_Simp_mkSimpContext_x27___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_mkSimpContext_x27___closed__1);
l_Lean_Meta_Simp_mkSimpContext_x27___closed__2 = _init_l_Lean_Meta_Simp_mkSimpContext_x27___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_mkSimpContext_x27___closed__2);
l_Lean_Meta_shouldPreprocess___closed__1 = _init_l_Lean_Meta_shouldPreprocess___closed__1();
lean_mark_persistent(l_Lean_Meta_shouldPreprocess___closed__1);
l_Lean_Meta_Simp_mkSimpTheoremsFromConst_x27___closed__1 = _init_l_Lean_Meta_Simp_mkSimpTheoremsFromConst_x27___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_mkSimpTheoremsFromConst_x27___closed__1);
l_Lean_Meta_Simp_addSimpAttr___closed__1 = _init_l_Lean_Meta_Simp_addSimpAttr___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_addSimpAttr___closed__1);
l_Lean_Meta_Simp_addSimpAttr___closed__2 = _init_l_Lean_Meta_Simp_addSimpAttr___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_addSimpAttr___closed__2);
l_Lean_Meta_Simp_addSimpAttrFromSyntax___closed__1 = _init_l_Lean_Meta_Simp_addSimpAttrFromSyntax___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_addSimpAttrFromSyntax___closed__1);
l_Lean_Meta_Simp_addSimpAttrFromSyntax___closed__2 = _init_l_Lean_Meta_Simp_addSimpAttrFromSyntax___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_addSimpAttrFromSyntax___closed__2);
l_Lean_Meta_Simp_addSimpAttrFromSyntax___closed__3 = _init_l_Lean_Meta_Simp_addSimpAttrFromSyntax___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_addSimpAttrFromSyntax___closed__3);
l_Lean_Meta_Simp_addSimpAttrFromSyntax___closed__4 = _init_l_Lean_Meta_Simp_addSimpAttrFromSyntax___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_addSimpAttrFromSyntax___closed__4);
l_Lean_Meta_Simp_addSimpAttrFromSyntax___closed__5 = _init_l_Lean_Meta_Simp_addSimpAttrFromSyntax___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_addSimpAttrFromSyntax___closed__5);
l_Lean_Meta_simpTheoremsOfNames___closed__1 = _init_l_Lean_Meta_simpTheoremsOfNames___closed__1();
lean_mark_persistent(l_Lean_Meta_simpTheoremsOfNames___closed__1);
l_Lean_Meta_simpOnlyNames___closed__1 = _init_l_Lean_Meta_simpOnlyNames___closed__1();
lean_mark_persistent(l_Lean_Meta_simpOnlyNames___closed__1);
l_Lean_Meta_simpEq___lambda__1___closed__1 = _init_l_Lean_Meta_simpEq___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_simpEq___lambda__1___closed__1);
l_Lean_Meta_simpEq___lambda__1___closed__2 = _init_l_Lean_Meta_simpEq___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_simpEq___lambda__1___closed__2);
l_Lean_Meta_simpEq___lambda__3___closed__1 = _init_l_Lean_Meta_simpEq___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_simpEq___lambda__3___closed__1);
l_Lean_Meta_simpEq___lambda__3___closed__2 = _init_l_Lean_Meta_simpEq___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Meta_simpEq___lambda__3___closed__2);
l_Lean_Meta_getAllSimpAttrs___closed__1 = _init_l_Lean_Meta_getAllSimpAttrs___closed__1();
lean_mark_persistent(l_Lean_Meta_getAllSimpAttrs___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
