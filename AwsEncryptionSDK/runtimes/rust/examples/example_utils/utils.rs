// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

pub const TEST_EXAMPLE_DATA: &str = "Hello World!";

pub const TEST_DEFAULT_KMS_KEY_ID: &str =
    "arn:aws:kms:us-west-2:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f";

pub const TEST_DEFAULT_KMS_KEY_ACCOUNT_ID: &str = "658956600833";

pub const TEST_SECOND_REGION_KMS_KEY_ID: &str =
    "arn:aws:kms:eu-central-1:658956600833:key/75414c93-5285-4b57-99c9-30c1cf0a22c2";

pub const TEST_KMS_RSA_KEY_ID: &str =
    "arn:aws:kms:us-west-2:370957321024:key/mrk-63d386cb70614ea59b32ad65c9315297";

pub const TEST_KMS_RSA_PUBLIC_KEY: &str = "-----BEGIN PUBLIC KEY-----\n\
                        MIIBIjANBgkqhkiG9w0BAQEFAAOCAQ8AMIIBCgKCAQEA27Uc/fBaMVhxCE/SpCMQ\
                        oSBRSzQJw+o2hBaA+FiPGtiJ/aPy7sn18aCkelaSj4kwoC79b/arNHlkjc7OJFsN\
                        /GoFKgNvaiY4lOeJqEiWQGSSgHtsJLdbO2u4OOSxh8qIRAMKbMgQDVX4FR/PLKeK\
                        fc2aCDvcNSpAM++8NlNmv7+xQBJydr5ce91eISbHkFRkK3/bAM+1iddupoRw4Wo2\
                        r3avzrg5xBHmzR7u1FTab22Op3Hgb2dBLZH43wNKAceVwKqKA8UNAxashFON7xK9\
                        yy4kfOL0Z/nhxRKe4jRZ/5v508qIzgzCksYy7Y3QbMejAtiYnr7s5/d5KWw0swou\
                        twIDAQAB\n\
                        -----END PUBLIC KEY-----";

pub const TEST_MRK_KEY_ID_US_EAST_1: &str =
    "arn:aws:kms:us-east-1:658956600833:key/mrk-80bd8ecdcd4342aebd84b7dc9da498a7";

pub const TEST_MRK_KEY_ID_EU_WEST_1: &str =
    "arn:aws:kms:eu-west-1:658956600833:key/mrk-80bd8ecdcd4342aebd84b7dc9da498a7";

pub const TEST_KEY_STORE_NAME: &str = "KeyStoreDdbTable";

pub const TEST_LOGICAL_KEY_STORE_NAME: &str = "KeyStoreDdbTable";

pub const TEST_KEY_STORE_KMS_KEY_ID: &str =
    "arn:aws:kms:us-west-2:370957321024:key/9d989aa2-2f9c-438c-a745-cc57d3ad0126";
