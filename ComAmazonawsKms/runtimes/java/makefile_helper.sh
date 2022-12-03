#!/bin/bash

if [[ "$1" == "implementation" ]]; then
    mkdir -p runtimes/java/src/main/dafny-generated
	for directory in runtimes/java/temp/ComAmazonawsKms-java/*; do
		mv "$directory" "runtimes/java/src/main/dafny-generated/"
	done
    exit 0
elif [[ "$1" == "test" ]]; then
    # With the runAllTests flag, dafny generates an entry point for the tests that we want,
    # so we copy all files to the test destination.
    mkdir -p runtimes/java/src/test/dafny-generated
    for allFiles in runtimes/java/temp-tests/ComAmazonawsKmsTests-java/*; do
		mv "$allFiles" "runtimes/java/src/test/dafny-generated/"
	done
    exit 0
else
    echo "makefile_helper needs either implementation or test argument"
    echo "i.e: ./runtimes/java/makefile_helper.sh test"
    exit 1
fi
