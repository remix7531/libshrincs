(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

From Shrincs.internal.ssprove.wots Require Import theorem.

Print Assumptions Shrincs.internal.ssprove.wots.theorem.shrincs_wots_secure.
Print Assumptions Shrincs.internal.ssprove.wots.theorem.shrincs_wots_secure_ideal_sk.
Print Assumptions SSProve.Crypt.nominal.Adv.Adv_triangle.
