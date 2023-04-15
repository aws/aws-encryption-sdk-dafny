// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.keyStore;

import Dafny.Aws.Cryptography.KeyStore.Types.*;
import Dafny.Aws.Cryptography.KeyStore.Types.Error;
import Dafny.Com.Amazonaws.Dynamodb.Types.IDynamoDBClient;
import Dafny.Com.Amazonaws.Kms.Types.IKMSClient;
import Wrappers_Compile.Option;
import dafny.DafnySequence;
import dafny.TypeDescriptor;
import java.lang.Byte;
import java.lang.Character;
import java.lang.RuntimeException;
import java.lang.String;
import java.util.List;
import java.util.Objects;
import software.amazon.cryptography.keyStore.model.CollectionOfErrors;
import software.amazon.cryptography.keyStore.model.KeyStoreException;
import software.amazon.cryptography.keyStore.model.OpaqueError;

public class ToDafny {

  public static IKeyStoreClient KeyStore(KeyStore nativeValue) {
    return nativeValue.impl();
  }

  public static Error Error(RuntimeException nativeValue) {
    if (nativeValue instanceof KeyStoreException) {
      return ToDafny.Error((KeyStoreException) nativeValue);
    }
    if (nativeValue instanceof OpaqueError) {
      return ToDafny.Error((OpaqueError) nativeValue);
    }
    if (nativeValue instanceof CollectionOfErrors) {
      return ToDafny.Error((CollectionOfErrors) nativeValue);
    }
    return Error.create_Opaque(nativeValue);
  }

  public static Error Error(OpaqueError nativeValue) {
    return Error.create_Opaque(nativeValue.obj());
  }

  public static Error Error(CollectionOfErrors nativeValue) {
    DafnySequence<? extends Error> list = software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
        nativeValue.list(), 
        ToDafny::Error, 
        Error._typeDescriptor());
    return Error.create_CollectionOfErrors(list);
  }

  public static CreateKeyInput CreateKeyInput(
      software.amazon.cryptography.keyStore.model.CreateKeyInput nativeValue) {
    DafnySequence<? extends Character> awsKmsKeyArn;
    awsKmsKeyArn = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.awsKmsKeyArn());
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> grantTokens;
    grantTokens = (Objects.nonNull(nativeValue.grantTokens()) && nativeValue.grantTokens().size() > 0) ?
        Option.create_Some(ToDafny.GrantTokenList(nativeValue.grantTokens()))
        : Option.create_None();
    return new CreateKeyInput(awsKmsKeyArn, grantTokens);
  }

  public static GetBeaconKeyOutput GetBeaconKeyOutput(
      software.amazon.cryptography.keyStore.model.GetBeaconKeyOutput nativeValue) {
    DafnySequence<? extends Character> beaconKeyIdentifier;
    beaconKeyIdentifier = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.beaconKeyIdentifier());
    DafnySequence<? extends Byte> beaconKey;
    beaconKey = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.beaconKey());
    return new GetBeaconKeyOutput(beaconKeyIdentifier, beaconKey);
  }

  public static CreateKeyStoreInput CreateKeyStoreInput(
      software.amazon.cryptography.keyStore.model.CreateKeyStoreInput nativeValue) {
    return new CreateKeyStoreInput();
  }

  public static GetBranchKeyVersionOutput GetBranchKeyVersionOutput(
      software.amazon.cryptography.keyStore.model.GetBranchKeyVersionOutput nativeValue) {
    DafnySequence<? extends Byte> branchKeyVersion;
    branchKeyVersion = software.amazon.dafny.conversion.ToDafny.Simple.DafnyUtf8Bytes(nativeValue.branchKeyVersion());
    DafnySequence<? extends Byte> branchKey;
    branchKey = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.branchKey());
    return new GetBranchKeyVersionOutput(branchKeyVersion, branchKey);
  }

  public static GetBranchKeyVersionInput GetBranchKeyVersionInput(
      software.amazon.cryptography.keyStore.model.GetBranchKeyVersionInput nativeValue) {
    DafnySequence<? extends Character> branchKeyIdentifier;
    branchKeyIdentifier = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.branchKeyIdentifier());
    DafnySequence<? extends Character> branchKeyVersion;
    branchKeyVersion = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.branchKeyVersion());
    Option<DafnySequence<? extends Character>> awsKmsKeyArn;
    awsKmsKeyArn = Objects.nonNull(nativeValue.awsKmsKeyArn()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.awsKmsKeyArn()))
        : Option.create_None();
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> grantTokens;
    grantTokens = (Objects.nonNull(nativeValue.grantTokens()) && nativeValue.grantTokens().size() > 0) ?
        Option.create_Some(ToDafny.GrantTokenList(nativeValue.grantTokens()))
        : Option.create_None();
    return new GetBranchKeyVersionInput(branchKeyIdentifier, branchKeyVersion, awsKmsKeyArn, grantTokens);
  }

  public static CreateKeyStoreOutput CreateKeyStoreOutput(
      software.amazon.cryptography.keyStore.model.CreateKeyStoreOutput nativeValue) {
    DafnySequence<? extends Character> tableArn;
    tableArn = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.tableArn());
    return new CreateKeyStoreOutput(tableArn);
  }

  public static GetBeaconKeyInput GetBeaconKeyInput(
      software.amazon.cryptography.keyStore.model.GetBeaconKeyInput nativeValue) {
    DafnySequence<? extends Character> branchKeyIdentifier;
    branchKeyIdentifier = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.branchKeyIdentifier());
    Option<DafnySequence<? extends Character>> awsKmsKeyArn;
    awsKmsKeyArn = Objects.nonNull(nativeValue.awsKmsKeyArn()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.awsKmsKeyArn()))
        : Option.create_None();
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> grantTokens;
    grantTokens = (Objects.nonNull(nativeValue.grantTokens()) && nativeValue.grantTokens().size() > 0) ?
        Option.create_Some(ToDafny.GrantTokenList(nativeValue.grantTokens()))
        : Option.create_None();
    return new GetBeaconKeyInput(branchKeyIdentifier, awsKmsKeyArn, grantTokens);
  }

  public static VersionKeyInput VersionKeyInput(
      software.amazon.cryptography.keyStore.model.VersionKeyInput nativeValue) {
    DafnySequence<? extends Character> branchKeyIdentifier;
    branchKeyIdentifier = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.branchKeyIdentifier());
    Option<DafnySequence<? extends Character>> awsKmsKeyArn;
    awsKmsKeyArn = Objects.nonNull(nativeValue.awsKmsKeyArn()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.awsKmsKeyArn()))
        : Option.create_None();
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> grantTokens;
    grantTokens = (Objects.nonNull(nativeValue.grantTokens()) && nativeValue.grantTokens().size() > 0) ?
        Option.create_Some(ToDafny.GrantTokenList(nativeValue.grantTokens()))
        : Option.create_None();
    return new VersionKeyInput(branchKeyIdentifier, awsKmsKeyArn, grantTokens);
  }

  public static CreateKeyOutput CreateKeyOutput(
      software.amazon.cryptography.keyStore.model.CreateKeyOutput nativeValue) {
    DafnySequence<? extends Character> branchKeyIdentifier;
    branchKeyIdentifier = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.branchKeyIdentifier());
    return new CreateKeyOutput(branchKeyIdentifier);
  }

  public static GetActiveBranchKeyOutput GetActiveBranchKeyOutput(
      software.amazon.cryptography.keyStore.model.GetActiveBranchKeyOutput nativeValue) {
    DafnySequence<? extends Byte> branchKeyVersion;
    branchKeyVersion = software.amazon.dafny.conversion.ToDafny.Simple.DafnyUtf8Bytes(nativeValue.branchKeyVersion());
    DafnySequence<? extends Byte> branchKey;
    branchKey = software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.branchKey());
    return new GetActiveBranchKeyOutput(branchKeyVersion, branchKey);
  }

  public static KeyStoreConfig KeyStoreConfig(
      software.amazon.cryptography.keyStore.model.KeyStoreConfig nativeValue) {
    Option<DafnySequence<? extends Character>> id;
    id = Objects.nonNull(nativeValue.id()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.id()))
        : Option.create_None();
    Option<DafnySequence<? extends Character>> ddbTableName;
    ddbTableName = Objects.nonNull(nativeValue.ddbTableName()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.ddbTableName()))
        : Option.create_None();
    Option<IDynamoDBClient> ddbClient;
    ddbClient = Objects.nonNull(nativeValue.ddbClient()) ?
        Option.create_Some(Dafny.Com.Amazonaws.Dynamodb.ToDafny.DynamoDB_20120810(nativeValue.ddbClient()))
        : Option.create_None();
    Option<IKMSClient> kmsClient;
    kmsClient = Objects.nonNull(nativeValue.kmsClient()) ?
        Option.create_Some(Dafny.Com.Amazonaws.Kms.ToDafny.TrentService(nativeValue.kmsClient()))
        : Option.create_None();
    return new KeyStoreConfig(id, ddbTableName, ddbClient, kmsClient);
  }

  public static GetActiveBranchKeyInput GetActiveBranchKeyInput(
      software.amazon.cryptography.keyStore.model.GetActiveBranchKeyInput nativeValue) {
    DafnySequence<? extends Character> branchKeyIdentifier;
    branchKeyIdentifier = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.branchKeyIdentifier());
    Option<DafnySequence<? extends Character>> awsKmsKeyArn;
    awsKmsKeyArn = Objects.nonNull(nativeValue.awsKmsKeyArn()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.awsKmsKeyArn()))
        : Option.create_None();
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> grantTokens;
    grantTokens = (Objects.nonNull(nativeValue.grantTokens()) && nativeValue.grantTokens().size() > 0) ?
        Option.create_Some(ToDafny.GrantTokenList(nativeValue.grantTokens()))
        : Option.create_None();
    return new GetActiveBranchKeyInput(branchKeyIdentifier, awsKmsKeyArn, grantTokens);
  }

  public static Error Error(KeyStoreException nativeValue) {
    DafnySequence<? extends Character> message;
    message = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.message());
    return new Error_KeyStoreException(message);
  }

  public static DafnySequence<? extends DafnySequence<? extends Character>> GrantTokenList(
      List<String> nativeValue) {
    return software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
        nativeValue, 
        software.amazon.dafny.conversion.ToDafny.Simple::CharacterSequence, 
        DafnySequence._typeDescriptor(TypeDescriptor.CHAR));
  }
}
