# lean 4 tutorials

[![Gitpod Ready-to-Code](https://img.shields.io/badge/Gitpod-ready--to--code-blue?logo=gitpod)](https://gitpod.io/#https://github.com/leanprover-community/tutorials4)

WIP port of the tutorials project to Lean 4.

The goal of this project is to quickly teach you how to use Lean 3 for
mathematics using a very hands-on approach. It can be used alongside
[Theorem proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)
or independently.

Currently, these tutorials do not cover creating your own theories, only
proving things in elementary real analysis. All exercises are adapted
from a first year undergraduate course by Patrick Massot in Orsay,
adding only explanations about compressing proofs using slightly advanced
tactics like `rintros` and `rcases`.

What you do need first is to install Lean 4 and get this project. [todo: add instructions]

Then, in the `Tutorials4/Tutorials` folder, create a copy of the exercises folder for you work.
This way it won't be overwritten if you update the project to get new exercises.
You can then open the tutorials folder in VS code.
For instance you can type:
```
cp -r tutorials4/Tutorials/Exercises tutorials4/Tutorials/MyExercises
code tutorials4
```
VSCode has a file explorer that you can open by clicking the top icon in
the icon column on the left. In this explorer, you can navigate to
`Tutorials/MyExercises` and click on `00FirstProofs.lean`.
This file does not contain any exercise, it is meant as an
overview of the basics. You can skip it if you are really eager to start
coding, but this is not recommended. You don't need to understand
everything while reading this file, only try to get a feel for what it's
looking like, and maybe start picking up some key words.

There are solutions for all the exercises in `Tutorials/Solutions`. If you
need help about any specific exercise, you can come on
[Zulip](https://leanprover.zulipchat.com) in the "new members" stream
and look for a thread called "tutorials4 NNNN" where NNNN is the exercise
number. If no such thread exists, you can create one!

## Not yet working

A list of things that don't work (yet) in Lean 4
* `linarith` gives many errors
* `set_option pp.parens true`