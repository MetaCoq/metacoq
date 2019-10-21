# Safe Checker

Implementation of a fuel-free, correct type checker for PCUIC.

| File                  | Description                                          |
|-----------------------|------------------------------------------------------|
| [PCUICSafeReduce]     | Weak-head reduction machine                          |
| [PCUICSafeConversion] | Conversion checker                                   |
| [PCUICSafeChecker]    | Type inference and type checking                     |
| [PCUICSafeRetyping]   | Fast type inference, assuming well-typedness         |
| [SafeTemplateChecker] |                                                      |
| [Loader]              |                                                      |
| [Extraction]          |                                                      |

[PCUICSafeReduce]: PCUICSafeReduce.v
[PCUICSafeConversion]: PCUICSafeConversion.v
[PCUICSafeChecker]: PCUICSafeChecker.v
[PCUICSafeRetyping]: PCUICSafeRetyping.v
[SafeTemplateChecker]: SafeTemplateChecker.v
[Loader]: Loader.v
[Extraction]: Extraction.v

All of these are proven correct but not yet complete.
They are suited for extraction which would remove the termination and
correctness proofs.
