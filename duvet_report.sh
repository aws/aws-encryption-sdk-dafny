#!/bin/sh

./aws-encryption-sdk-specification/util/report.js $(find src -name '*.dfy') $(find test -name '*.dfy') $(find compliance_exceptions -name '*.txt')
