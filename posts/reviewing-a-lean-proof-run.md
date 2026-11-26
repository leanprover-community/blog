---
author: 'TheoremOS maintainers'
category: 'Tutorial'
date: 2026-11-26 18:28:00 UTC+08:00
description: 'Check the formal statements and the saved Lean verification for each original goal.'
has_math: false
slug: reviewing-a-lean-proof-run
tags: 'Lean 4, verification'
title: 'What did the Lean run actually prove?'
type: text
---
You ask for two theorems, get a Lean file back, and see that it compiles. Did the file still contain both theorems with their original statements? To answer that, write down the expected declarations before looking at the proof, then look for a check against each of those declarations.

This walkthrough uses a small example from TheoremOS, a Lean 4 workbench and Linux CLI. It was prepared with Codex on behalf of the project maintainers. You can follow a recording in the browser without installing Lean or providing a model key. A separate local replay runs Lean. [Open the exercise](https://app.theoremos.top/practice.html?lang=en) · [TheoremOS source](https://github.com/HuggingMath/theorem-os)

<!-- TEASER_END -->

## Start with the declarations

The informal request is to show that adding zero on either side leaves every natural number unchanged. The exercise gives the two targets names:

| Declaration | Proposition for `n : Nat` |
| --- | --- |
| `Tutorial.add_zero` | `n + 0 = n` |
| `Tutorial.zero_add` | `0 + n = n` |

Review this list first. For a real problem, check the domains, quantifiers and hypotheses before asking an agent to work on it. The kernel can check a proof of the formal statement it receives. A collaborator still has to decide whether that statement expresses the original question.

## Follow a failure, then an omission

Open the exercise, choose **Inspect a direct attempt**, then select **Approve plan v1**. Under **Inspect the first attempt**, compare the two goals and expand **Inspect the failed candidate**. The preset candidate tries `rfl` in both declarations. Lean's definition of `Nat.add` recurses on its second argument, so `n + 0` reduces to `n`. With `0 + n`, that argument is a variable. The same tactic leaves an unsolved goal.

In **Guide the left-addition repair**, select the option to submit only the proved right-addition goal, then click **Send guidance**. The exercise declines the request because it drops `Tutorial.zero_add` from the approved plan. Now choose the repair with `Nat.zero_add` and send it. Open **Read the check receipts** to see one saved Lean check for each declaration. You can save the receipt references and select **Download exercise record** to keep them with your choices. The export identifies this as a recording made available for the exercise.

![TheoremOS workbench with the Lean problem input and execution settings](https://raw.githubusercontent.com/HuggingMath/theorem-os/main/docs/assets/workbench-desktop-en.png)

## Let Lean run the checks locally

Prepare a Linux host with Git, Bun, Node.js, Elan and the other prerequisites, then run the following from a fresh directory. The example has a separate math configuration and uses the Lean 4.33.0 toolchain. [Linux getting started guide](https://github.com/HuggingMath/theorem-os/blob/main/examples/getting-started/README.md)

```sh
git clone https://github.com/HuggingMath/theorem-os.git
cd theorem-os
bun install --frozen-lockfile
elan toolchain install leanprover/lean4:v4.33.0
touch ../theoremos-lean-demo.env
export DEEPSCIENTIST_MATH_ENV_FILE="$PWD/../theoremos-lean-demo.env"
bun run math example replay --dir ../lean-verification-demo
bun run math inspect --run ../lean-verification-demo/result.json
```

The replay runs the deliberately failing candidate, the repaired candidate, and a separate whole-problem check. In the recorded local run, the candidate checks returned `false` and then `true`. The final result was `evaluated_passed`, with `kernel_verified` for both `Tutorial.add_zero` and `Tutorial.zero_add`. The two candidates were supplied with the example, and the result records a local Lean verification without a model call. [Download the 72-second CLI recording](https://raw.githubusercontent.com/HuggingMath/theorem-os/refs/heads/promo/opensrcs-linux-replay/docs/assets/theoremos-linux-replay.mp4)

For another Lean project, keep the original statements and build the intended module. Use `#print axioms` on each checked declaration if you need to inspect what it depends on. The Lean reference explains how to interpret `sorryAx`, standard axioms and custom axioms. [Validating a Lean proof](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
