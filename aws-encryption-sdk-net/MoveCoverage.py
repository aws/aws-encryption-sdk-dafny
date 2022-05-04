# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
import os
import shutil

ROOT_DIR = os.path.join("Test", "TestResults")

def move_coverage():
    """
    Move coverage.cobertura.xml from randomly named folder generated
    by Coverlet to stable file path for usage.
    """
    for subdir, dirs, files in os.walk(ROOT_DIR):
        for file in files:
            if file == 'coverage.cobertura.xml':
                shutil.move(os.path.join(subdir, file), os.path.join(ROOT_DIR, file))
                
def main():
    move_coverage()

if __name__ == "__main__":
    main()
    
