// Lean compiler output
// Module: CausalQIF.Certificates.PACBounds
// Imports: public import Init public import Mathlib.Data.Fin.Basic public import Mathlib.Data.Real.Basic public import Mathlib.Analysis.SpecialFunctions.Log.Basic public import Mathlib.Tactic.Linarith
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
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00NNReal_instSemiring_spec__1_spec__2_spec__3(lean_object*);
LEAN_EXPORT lean_object* lp_causal__qif_Nat_cast___at___00CausalQIF_spikeL1Distance_spec__0(lean_object*);
static lean_once_cell_t lp_causal__qif_CausalQIF_spikeL1Distance___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_causal__qif_CausalQIF_spikeL1Distance___redArg___closed__0;
LEAN_EXPORT lean_object* lp_causal__qif_CausalQIF_spikeL1Distance___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_causal__qif_CausalQIF_spikeL1Distance___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_causal__qif_CausalQIF_spikeL1Distance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_causal__qif_CausalQIF_spikeL1Distance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_causal__qif___private_CausalQIF_Certificates_PACBounds_0__CausalQIF_spikeL1Distance_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_causal__qif___private_CausalQIF_Certificates_PACBounds_0__CausalQIF_spikeL1Distance_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_causal__qif___private_CausalQIF_Certificates_PACBounds_0__CausalQIF_spikeL1Distance_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_causal__qif_Nat_cast___at___00CausalQIF_spikeL1Distance_spec__0(lean_object* v_a_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00NNReal_instSemiring_spec__1_spec__2_spec__3(v_a_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_causal__qif_CausalQIF_spikeL1Distance___redArg___closed__0(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_unsigned_to_nat(2u);
v___x_4_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00NNReal_instSemiring_spec__1_spec__2_spec__3(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_causal__qif_CausalQIF_spikeL1Distance___redArg(lean_object* v_alpha_5_, lean_object* v_tau_6_, lean_object* v_x_7_, lean_object* v_x_8_){
_start:
{
if (lean_obj_tag(v_x_7_) == 0)
{
if (lean_obj_tag(v_x_8_) == 0)
{
lean_object* v___x_9_; 
lean_dec(v_tau_6_);
lean_dec(v_alpha_5_);
v___x_9_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
return v___x_9_;
}
else
{
lean_object* v___f_10_; 
v___f_10_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_10_, 0, v_alpha_5_);
lean_closure_set(v___f_10_, 1, v_tau_6_);
return v___f_10_;
}
}
else
{
if (lean_obj_tag(v_x_8_) == 0)
{
lean_object* v___f_11_; 
v___f_11_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_11_, 0, v_alpha_5_);
lean_closure_set(v___f_11_, 1, v_tau_6_);
return v___f_11_;
}
else
{
lean_object* v_val_12_; lean_object* v_val_13_; uint8_t v___x_14_; 
v_val_12_ = lean_ctor_get(v_x_7_, 0);
v_val_13_ = lean_ctor_get(v_x_8_, 0);
v___x_14_ = lean_nat_dec_eq(v_val_12_, v_val_13_);
if (v___x_14_ == 0)
{
lean_object* v___x_15_; lean_object* v___f_16_; lean_object* v___f_17_; 
v___x_15_ = lean_obj_once(&lp_causal__qif_CausalQIF_spikeL1Distance___redArg___closed__0, &lp_causal__qif_CausalQIF_spikeL1Distance___redArg___closed__0_once, _init_lp_causal__qif_CausalQIF_spikeL1Distance___redArg___closed__0);
v___f_16_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_16_, 0, v___x_15_);
lean_closure_set(v___f_16_, 1, v_alpha_5_);
v___f_17_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_17_, 0, v___f_16_);
lean_closure_set(v___f_17_, 1, v_tau_6_);
return v___f_17_;
}
else
{
lean_object* v___x_18_; 
lean_dec(v_tau_6_);
lean_dec(v_alpha_5_);
v___x_18_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
return v___x_18_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_causal__qif_CausalQIF_spikeL1Distance___redArg___boxed(lean_object* v_alpha_19_, lean_object* v_tau_20_, lean_object* v_x_21_, lean_object* v_x_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = lp_causal__qif_CausalQIF_spikeL1Distance___redArg(v_alpha_19_, v_tau_20_, v_x_21_, v_x_22_);
lean_dec(v_x_22_);
lean_dec(v_x_21_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* lp_causal__qif_CausalQIF_spikeL1Distance(lean_object* v_K_24_, lean_object* v_alpha_25_, lean_object* v_tau_26_, lean_object* v_x_27_, lean_object* v_x_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = lp_causal__qif_CausalQIF_spikeL1Distance___redArg(v_alpha_25_, v_tau_26_, v_x_27_, v_x_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* lp_causal__qif_CausalQIF_spikeL1Distance___boxed(lean_object* v_K_30_, lean_object* v_alpha_31_, lean_object* v_tau_32_, lean_object* v_x_33_, lean_object* v_x_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = lp_causal__qif_CausalQIF_spikeL1Distance(v_K_30_, v_alpha_31_, v_tau_32_, v_x_33_, v_x_34_);
lean_dec(v_x_34_);
lean_dec(v_x_33_);
lean_dec(v_K_30_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* lp_causal__qif___private_CausalQIF_Certificates_PACBounds_0__CausalQIF_spikeL1Distance_match__1_splitter___redArg(lean_object* v_x_36_, lean_object* v_x_37_, lean_object* v_h__1_38_, lean_object* v_h__2_39_, lean_object* v_h__3_40_, lean_object* v_h__4_41_){
_start:
{
if (lean_obj_tag(v_x_36_) == 0)
{
lean_dec(v_h__4_41_);
lean_dec(v_h__3_40_);
if (lean_obj_tag(v_x_37_) == 0)
{
lean_object* v___x_42_; lean_object* v___x_43_; 
lean_dec(v_h__2_39_);
v___x_42_ = lean_box(0);
v___x_43_ = lean_apply_1(v_h__1_38_, v___x_42_);
return v___x_43_;
}
else
{
lean_object* v_val_44_; lean_object* v___x_45_; 
lean_dec(v_h__1_38_);
v_val_44_ = lean_ctor_get(v_x_37_, 0);
lean_inc(v_val_44_);
lean_dec_ref(v_x_37_);
v___x_45_ = lean_apply_1(v_h__2_39_, v_val_44_);
return v___x_45_;
}
}
else
{
lean_dec(v_h__2_39_);
lean_dec(v_h__1_38_);
if (lean_obj_tag(v_x_37_) == 0)
{
lean_object* v_val_46_; lean_object* v___x_47_; 
lean_dec(v_h__4_41_);
v_val_46_ = lean_ctor_get(v_x_36_, 0);
lean_inc(v_val_46_);
lean_dec_ref(v_x_36_);
v___x_47_ = lean_apply_1(v_h__3_40_, v_val_46_);
return v___x_47_;
}
else
{
lean_object* v_val_48_; lean_object* v_val_49_; lean_object* v___x_50_; 
lean_dec(v_h__3_40_);
v_val_48_ = lean_ctor_get(v_x_36_, 0);
lean_inc(v_val_48_);
lean_dec_ref(v_x_36_);
v_val_49_ = lean_ctor_get(v_x_37_, 0);
lean_inc(v_val_49_);
lean_dec_ref(v_x_37_);
v___x_50_ = lean_apply_2(v_h__4_41_, v_val_48_, v_val_49_);
return v___x_50_;
}
}
}
}
LEAN_EXPORT lean_object* lp_causal__qif___private_CausalQIF_Certificates_PACBounds_0__CausalQIF_spikeL1Distance_match__1_splitter(lean_object* v_K_51_, lean_object* v_motive_52_, lean_object* v_x_53_, lean_object* v_x_54_, lean_object* v_h__1_55_, lean_object* v_h__2_56_, lean_object* v_h__3_57_, lean_object* v_h__4_58_){
_start:
{
if (lean_obj_tag(v_x_53_) == 0)
{
lean_dec(v_h__4_58_);
lean_dec(v_h__3_57_);
if (lean_obj_tag(v_x_54_) == 0)
{
lean_object* v___x_59_; lean_object* v___x_60_; 
lean_dec(v_h__2_56_);
v___x_59_ = lean_box(0);
v___x_60_ = lean_apply_1(v_h__1_55_, v___x_59_);
return v___x_60_;
}
else
{
lean_object* v_val_61_; lean_object* v___x_62_; 
lean_dec(v_h__1_55_);
v_val_61_ = lean_ctor_get(v_x_54_, 0);
lean_inc(v_val_61_);
lean_dec_ref(v_x_54_);
v___x_62_ = lean_apply_1(v_h__2_56_, v_val_61_);
return v___x_62_;
}
}
else
{
lean_dec(v_h__2_56_);
lean_dec(v_h__1_55_);
if (lean_obj_tag(v_x_54_) == 0)
{
lean_object* v_val_63_; lean_object* v___x_64_; 
lean_dec(v_h__4_58_);
v_val_63_ = lean_ctor_get(v_x_53_, 0);
lean_inc(v_val_63_);
lean_dec_ref(v_x_53_);
v___x_64_ = lean_apply_1(v_h__3_57_, v_val_63_);
return v___x_64_;
}
else
{
lean_object* v_val_65_; lean_object* v_val_66_; lean_object* v___x_67_; 
lean_dec(v_h__3_57_);
v_val_65_ = lean_ctor_get(v_x_53_, 0);
lean_inc(v_val_65_);
lean_dec_ref(v_x_53_);
v_val_66_ = lean_ctor_get(v_x_54_, 0);
lean_inc(v_val_66_);
lean_dec_ref(v_x_54_);
v___x_67_ = lean_apply_2(v_h__4_58_, v_val_65_, v_val_66_);
return v___x_67_;
}
}
}
}
LEAN_EXPORT lean_object* lp_causal__qif___private_CausalQIF_Certificates_PACBounds_0__CausalQIF_spikeL1Distance_match__1_splitter___boxed(lean_object* v_K_68_, lean_object* v_motive_69_, lean_object* v_x_70_, lean_object* v_x_71_, lean_object* v_h__1_72_, lean_object* v_h__2_73_, lean_object* v_h__3_74_, lean_object* v_h__4_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = lp_causal__qif___private_CausalQIF_Certificates_PACBounds_0__CausalQIF_spikeL1Distance_match__1_splitter(v_K_68_, v_motive_69_, v_x_70_, v_x_71_, v_h__1_72_, v_h__2_73_, v_h__3_74_, v_h__4_75_);
lean_dec(v_K_68_);
return v_res_76_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Fin_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Real_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Log_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Tactic_Linarith(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_causal__qif_CausalQIF_Certificates_PACBounds(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Fin_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Real_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Log_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Tactic_Linarith(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
