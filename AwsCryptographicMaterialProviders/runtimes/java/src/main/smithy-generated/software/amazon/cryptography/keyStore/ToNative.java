// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.keystore;

import dafny.DafnySequence;
import java.lang.Character;
import java.lang.RuntimeException;
import java.lang.String;
import java.util.List;
import software.amazon.cryptography.keystore.internaldafny.types.Error;
import software.amazon.cryptography.keystore.internaldafny.types.Error_CollectionOfErrors;
import software.amazon.cryptography.keystore.internaldafny.types.Error_KeyStoreException;
import software.amazon.cryptography.keystore.internaldafny.types.Error_Opaque;
import software.amazon.cryptography.keystore.internaldafny.types.IKeyStoreClient;
import software.amazon.cryptography.keystore.model.BranchKeyStatusResolutionInput;
import software.amazon.cryptography.keystore.model.CollectionOfErrors;
import software.amazon.cryptography.keystore.model.CreateKeyOutput;
import software.amazon.cryptography.keystore.model.CreateKeyStoreInput;
import software.amazon.cryptography.keystore.model.CreateKeyStoreOutput;
import software.amazon.cryptography.keystore.model.GetActiveBranchKeyInput;
import software.amazon.cryptography.keystore.model.GetActiveBranchKeyOutput;
import software.amazon.cryptography.keystore.model.GetBeaconKeyInput;
import software.amazon.cryptography.keystore.model.GetBeaconKeyOutput;
import software.amazon.cryptography.keystore.model.GetBranchKeyVersionInput;
import software.amazon.cryptography.keystore.model.GetBranchKeyVersionOutput;
import software.amazon.cryptography.keystore.model.GetKeyStoreInfoOutput;
import software.amazon.cryptography.keystore.model.KMSConfiguration;
import software.amazon.cryptography.keystore.model.KeyStoreConfig;
import software.amazon.cryptography.keystore.model.KeyStoreException;
import software.amazon.cryptography.keystore.model.OpaqueError;
import software.amazon.cryptography.keystore.model.VersionKeyInput;

public class ToNative {
  public static OpaqueError Error(Error_Opaque dafnyValue) {
    OpaqueError.Builder nativeBuilder = OpaqueError.builder();
    nativeBuilder.obj(dafnyValue.dtor_obj());
    return nativeBuilder.build();
  }

  public static CollectionOfErrors Error(Error_CollectionOfErrors dafnyValue) {
    CollectionOfErrors.Builder nativeBuilder = CollectionOfErrors.builder();
    nativeBuilder.list(
        software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue.dtor_list(), 
        ToNative::Error));
    return nativeBuilder.build();
  }

  public static KeyStoreException Error(Error_KeyStoreException dafnyValue) {
    KeyStoreException.Builder nativeBuilder = KeyStoreException.builder();
    nativeBuilder.message(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message()));
    return nativeBuilder.build();
  }

  public static RuntimeException Error(Error dafnyValue) {
    if (dafnyValue.is_KeyStoreException()) {
      return ToNative.Error((Error_KeyStoreException) dafnyValue);
    }
    if (dafnyValue.is_Opaque()) {
      return ToNative.Error((Error_Opaque) dafnyValue);
    }
    if (dafnyValue.is_CollectionOfErrors()) {
      return ToNative.Error((Error_CollectionOfErrors) dafnyValue);
    }
    if (dafnyValue.is_ComAmazonawsDynamodb()) {
      return software.amazon.cryptography.services.dynamodb.internaldafny.ToNative.Error(dafnyValue.dtor_ComAmazonawsDynamodb());
    }
    if (dafnyValue.is_ComAmazonawsKms()) {
      return software.amazon.cryptography.services.kms.internaldafny.ToNative.Error(dafnyValue.dtor_ComAmazonawsKms());
    }
    OpaqueError.Builder nativeBuilder = OpaqueError.builder();
    nativeBuilder.obj(dafnyValue);
    return nativeBuilder.build();
  }

  public static BranchKeyStatusResolutionInput BranchKeyStatusResolutionInput(
      software.amazon.cryptography.keystore.internaldafny.types.BranchKeyStatusResolutionInput dafnyValue) {
    BranchKeyStatusResolutionInput.Builder nativeBuilder = BranchKeyStatusResolutionInput.builder();
    nativeBuilder.branchKeyIdentifier(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_branchKeyIdentifier()));
    return nativeBuilder.build();
  }

  public static CreateKeyOutput CreateKeyOutput(
      software.amazon.cryptography.keystore.internaldafny.types.CreateKeyOutput dafnyValue) {
    CreateKeyOutput.Builder nativeBuilder = CreateKeyOutput.builder();
    nativeBuilder.branchKeyIdentifier(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_branchKeyIdentifier()));
    return nativeBuilder.build();
  }

  public static CreateKeyStoreInput CreateKeyStoreInput(
      software.amazon.cryptography.keystore.internaldafny.types.CreateKeyStoreInput dafnyValue) {
    CreateKeyStoreInput.Builder nativeBuilder = CreateKeyStoreInput.builder();
    return nativeBuilder.build();
  }

  public static CreateKeyStoreOutput CreateKeyStoreOutput(
      software.amazon.cryptography.keystore.internaldafny.types.CreateKeyStoreOutput dafnyValue) {
    CreateKeyStoreOutput.Builder nativeBuilder = CreateKeyStoreOutput.builder();
    nativeBuilder.tableArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_tableArn()));
    return nativeBuilder.build();
  }

  public static GetActiveBranchKeyInput GetActiveBranchKeyInput(
      software.amazon.cryptography.keystore.internaldafny.types.GetActiveBranchKeyInput dafnyValue) {
    GetActiveBranchKeyInput.Builder nativeBuilder = GetActiveBranchKeyInput.builder();
    nativeBuilder.branchKeyIdentifier(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_branchKeyIdentifier()));
    return nativeBuilder.build();
  }

  public static GetActiveBranchKeyOutput GetActiveBranchKeyOutput(
      software.amazon.cryptography.keystore.internaldafny.types.GetActiveBranchKeyOutput dafnyValue) {
    GetActiveBranchKeyOutput.Builder nativeBuilder = GetActiveBranchKeyOutput.builder();
    nativeBuilder.branchKeyVersion(software.amazon.dafny.conversion.ToNative.Simple.DafnyUtf8Bytes(dafnyValue.dtor_branchKeyVersion()));
    nativeBuilder.branchKey(software.amazon.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_branchKey()));
    return nativeBuilder.build();
  }

  public static GetBeaconKeyInput GetBeaconKeyInput(
      software.amazon.cryptography.keystore.internaldafny.types.GetBeaconKeyInput dafnyValue) {
    GetBeaconKeyInput.Builder nativeBuilder = GetBeaconKeyInput.builder();
    nativeBuilder.branchKeyIdentifier(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_branchKeyIdentifier()));
    return nativeBuilder.build();
  }

  public static GetBeaconKeyOutput GetBeaconKeyOutput(
      software.amazon.cryptography.keystore.internaldafny.types.GetBeaconKeyOutput dafnyValue) {
    GetBeaconKeyOutput.Builder nativeBuilder = GetBeaconKeyOutput.builder();
    nativeBuilder.beaconKeyIdentifier(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_beaconKeyIdentifier()));
    nativeBuilder.beaconKey(software.amazon.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_beaconKey()));
    return nativeBuilder.build();
  }

  public static GetBranchKeyVersionInput GetBranchKeyVersionInput(
      software.amazon.cryptography.keystore.internaldafny.types.GetBranchKeyVersionInput dafnyValue) {
    GetBranchKeyVersionInput.Builder nativeBuilder = GetBranchKeyVersionInput.builder();
    nativeBuilder.branchKeyIdentifier(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_branchKeyIdentifier()));
    nativeBuilder.branchKeyVersion(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_branchKeyVersion()));
    return nativeBuilder.build();
  }

  public static GetBranchKeyVersionOutput GetBranchKeyVersionOutput(
      software.amazon.cryptography.keystore.internaldafny.types.GetBranchKeyVersionOutput dafnyValue) {
    GetBranchKeyVersionOutput.Builder nativeBuilder = GetBranchKeyVersionOutput.builder();
    nativeBuilder.branchKeyVersion(software.amazon.dafny.conversion.ToNative.Simple.DafnyUtf8Bytes(dafnyValue.dtor_branchKeyVersion()));
    nativeBuilder.branchKey(software.amazon.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_branchKey()));
    return nativeBuilder.build();
  }

  public static GetKeyStoreInfoOutput GetKeyStoreInfoOutput(
      software.amazon.cryptography.keystore.internaldafny.types.GetKeyStoreInfoOutput dafnyValue) {
    GetKeyStoreInfoOutput.Builder nativeBuilder = GetKeyStoreInfoOutput.builder();
    nativeBuilder.keyStoreId(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_keyStoreId()));
    nativeBuilder.keyStoreName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_keyStoreName()));
    nativeBuilder.logicalKeyStoreName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_logicalKeyStoreName()));
    nativeBuilder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_grantTokens()));
    nativeBuilder.kmsConfiguration(ToNative.KMSConfiguration(dafnyValue.dtor_kmsConfiguration()));
    return nativeBuilder.build();
  }

  public static KeyStoreConfig KeyStoreConfig(
      software.amazon.cryptography.keystore.internaldafny.types.KeyStoreConfig dafnyValue) {
    KeyStoreConfig.Builder nativeBuilder = KeyStoreConfig.builder();
    nativeBuilder.ddbTableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ddbTableName()));
    nativeBuilder.kmsConfiguration(ToNative.KMSConfiguration(dafnyValue.dtor_kmsConfiguration()));
    nativeBuilder.logicalKeyStoreName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_logicalKeyStoreName()));
    if (dafnyValue.dtor_id().is_Some()) {
      nativeBuilder.id(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_id().dtor_value()));
    }
    if (dafnyValue.dtor_grantTokens().is_Some()) {
      nativeBuilder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_grantTokens().dtor_value()));
    }
    if (dafnyValue.dtor_ddbClient().is_Some()) {
      nativeBuilder.ddbClient(software.amazon.cryptography.services.dynamodb.internaldafny.ToNative.DynamoDB_20120810(dafnyValue.dtor_ddbClient().dtor_value()));
    }
    if (dafnyValue.dtor_kmsClient().is_Some()) {
      nativeBuilder.kmsClient(software.amazon.cryptography.services.kms.internaldafny.ToNative.TrentService(dafnyValue.dtor_kmsClient().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static VersionKeyInput VersionKeyInput(
      software.amazon.cryptography.keystore.internaldafny.types.VersionKeyInput dafnyValue) {
    VersionKeyInput.Builder nativeBuilder = VersionKeyInput.builder();
    nativeBuilder.branchKeyIdentifier(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_branchKeyIdentifier()));
    return nativeBuilder.build();
  }

  public static KMSConfiguration KMSConfiguration(
      software.amazon.cryptography.keystore.internaldafny.types.KMSConfiguration dafnyValue) {
    KMSConfiguration.Builder nativeBuilder = KMSConfiguration.builder();
    if (dafnyValue.is_kmsKeyArn()) {
      nativeBuilder.kmsKeyArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_kmsKeyArn()));
    }
    return nativeBuilder.build();
  }

  public static List<String> GrantTokenList(
      DafnySequence<? extends DafnySequence<? extends Character>> dafnyValue) {
    return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue, 
        software.amazon.dafny.conversion.ToNative.Simple::String);
  }

  public static KeyStore KeyStore(IKeyStoreClient dafnyValue) {
    return new KeyStore(dafnyValue);
  }
}
