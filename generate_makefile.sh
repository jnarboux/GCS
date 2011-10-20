#!/bin/sh
coq_makefile -o Makefile -R . GCS Environment.v GenerateUOT.v Notations.v Signature.v Syntax.v test.v
