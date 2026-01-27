Please read the tex files in the folder blueprint/src/chapters, in the order of 
1. foundational-locale-theory.tex
2. zariski-locale.tex
3. functoriality.tex
4. structure-sheaf.tex
5. chapters/locally-ringed-locale.tex
6. chapters/basic-properties.tex

First fix all theorems tags and \lean{} tags that does not exists.

Then create a file for each of the tex file in the folder PointlessScheme.

For each chapter:
1. First formalize every statement in the a chapter (proof left sorry, definition and necessary intances must be filled). You cannot use axioms.
2. Then fix the errors and make sure the whole file with only statements and definitions pass the Lean compiler. Check that their semantic meaning aligns with the blueprint.
3. Mark \lean{} in blueprint with the full name of Lean declarations and mark the statements with \leanok in the blueprint.
4. Prove every sorry in the statements, fix every error. You cannot use axioms. For each sorry proved, mark the proof with \leanok in the lean blueprint. If you find some previous statements is wrong or formalized incorrectly, fix them and the tags before you do anything else.
