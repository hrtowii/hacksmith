```isabelle
theory Example
imports Main
begin

datatype HeartbeatMessageType = TLS1_HB_REQUEST | TLS1_HB_RESPONSE

record HeartbeatMessage =
  hb_type :: HeartbeatMessageType
  payload_length :: nat
  payload :: "nat list"
  padding :: "nat list"

definition MINIMUM_PADDING :: nat where
  "MINIMUM_PADDING = 16"

definition buggy_process_heartbeat :: "nat \<Rightarrow> nat \<Rightarrow> HeartbeatMessageType \<Rightarrow> nat list \<Rightarrow> (nat list) option" where
  "buggy_process_heartbeat claimed_payload actual_payload hbtype pl =
    (if hbtype = TLS1_HB_REQUEST then
      let padding = MINIMUM_PADDING;
          buffer_size = 1 + 2 + claimed_payload + padding;
          copied_payload = take claimed_payload pl
      in Some copied_payload
    else None)"

lemma buggy_no_unchecked_memcpy:
  "\<forall>claimed actual hbtype pl.
    buggy_process_heartbeat claimed actual hbtype pl \<noteq> None \<longrightarrow>
    claimed \<le> actual"
  apply(auto simp: buggy_process_heartbeat_def MINIMUM_PADDING_def split: if_splits)
  nitpick
  oops

definition fixed_process_heartbeat :: "nat \<Rightarrow> nat \<Rightarrow> HeartbeatMessageType \<Rightarrow> nat list \<Rightarrow> (nat list) option" where
  "fixed_process_heartbeat claimed_payload actual_payload hbtype pl =
    (if hbtype = TLS1_HB_REQUEST \<and> claimed_payload \<le> actual_payload then
      let padding = MINIMUM_PADDING;
          buffer_size = 1 + 2 + claimed_payload + padding;
          copied_payload = take claimed_payload pl
      in Some copied_payload
    else None)"

lemma fixed_no_unchecked_memcpy:
  "\<forall>claimed actual hbtype pl.
    fixed_process_heartbeat claimed actual hbtype pl \<noteq> None \<longrightarrow>
    claimed \<le> actual"
  by(auto simp: fixed_process_heartbeat_def MINIMUM_PADDING_def split: if_splits)

end
```