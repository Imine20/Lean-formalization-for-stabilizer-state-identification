# Independent V3 evidence tool review
Reviewer: group_order, read-only; reviewed after the mathematical package was frozen.
Frozen source: a741ad2633d99a28fb4bbbe86e3a9a0ac5b7970b.
The extractor and snapshot verifier are byte-identical to V2. The strict verifier only adds paperStochasticGroup_order and criticalSpectralMass to the original three mandatory main bodies, and changes the bundle identity/path to V3. No prior check was removed or weakened.
All tool and parent-tool hashes match the manifest. Manifest SHA256: 12beee2fc13c1ec393f4357397e190f6af4cd423035e9ab77927a4486c26482f.
Independent read-only execution of test_closure_controls.py exited zero and matched the stored result: 35 constant/35 original-body checks; deleting any of the five mandatory main body markers causes ValueError rejection.
The initial test harness caught the wrong exception type; fixing its capture did not change the verifier or its rejection.
This is a tool review and control test, not acceptance of the fresh full release currently running. Human mathematical review is outstanding.
