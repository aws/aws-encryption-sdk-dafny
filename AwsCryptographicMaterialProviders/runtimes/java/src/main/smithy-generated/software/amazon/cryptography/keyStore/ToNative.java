// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.keyStore;

import Dafny.Aws.Cryptography.KeyStore.Types.Error;
import Dafny.Aws.Cryptography.KeyStore.Types.Error_CollectionOfErrors;
import Dafny.Aws.Cryptography.KeyStore.Types.Error_KeyStoreException;
import Dafny.Aws.Cryptography.KeyStore.Types.Error_Opaque;
import Dafny.Aws.Cryptography.KeyStore.Types.IKeyStoreClient;
import dafny.DafnySequence;
import java.lang.Character;
import java.lang.RuntimeException;
import java.lang.String;
import java.util.List;
import software.amazon.cryptography.keyStore.model.BranchKeyStatusResolutionInput;
import software.amazon.cryptography.keyStore.model.CollectionOfErrors;
import software.amazon.cryptography.keyStore.model.CreateKeyInput;
import software.amazon.cryptography.keyStore.model.CreateKeyOutput;
import software.amazon.cryptography.keyStore.model.CreateKeyStoreInput;
import software.amazon.cryptography.keyStore.model.CreateKeyStoreOutput;
import software.amazon.cryptography.keyStore.model.GetActiveBranchKeyInput;
import software.amazon.cryptography.keyStore.model.GetActiveBranchKeyOutput;
import software.amazon.cryptography.keyStore.model.GetBeaconKeyInput;
import software.amazon.cryptography.keyStore.model.GetBeaconKeyOutput;
import software.amazon.cryptography.keyStore.model.GetBranchKeyVersionInput;
import software.amazon.cryptography.keyStore.model.GetBranchKeyVersionOutput;
import software.amazon.cryptography.keyStore.model.KeyStoreConfig;
import software.amazon.cryptography.keyStore.model.KeyStoreException;
import software.amazon.cryptography.keyStore.model.OpaqueError;
import software.amazon.cryptography.keyStore.model.VersionKeyInput;

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
    // BEGIN MANUAL EDIT
    if (dafnyValue.is_ComAmazonawsDynamodb()) {
      return Dafny.Com.Amazonaws.Dynamodb.ToNative.Error(dafnyValue.dtor_ComAmazonawsDynamodb());
    }
    if (dafnyValue.is_ComAmazonawsKms()) {
      return Dafny.Com.Amazonaws.Kms.ToNative.Error(dafnyValue.dtor_ComAmazonawsKms());
    }
    // END MANUAL EDIT
    if (dafnyValue.is_Opaque()) {
      return ToNative.Error((Error_Opaque) dafnyValue);
    }
    if (dafnyValue.is_CollectionOfErrors()) {
      return ToNative.Error((Error_CollectionOfErrors) dafnyValue);
    }
    OpaqueError.Builder nativeBuilder = OpaqueError.builder();
    nativeBuilder.obj(dafnyValue);
    return nativeBuilder.build();
  }

  public static CreateKeyInput CreateKeyInput(
      Dafny.Aws.Cryptography.KeyStore.Types.CreateKeyInput dafnyValue) {
    CreateKeyInput.Builder nativeBuilder = CreateKeyInput.builder();
    if (dafnyValue.dtor_grantTokens().is_Some()) {
      nativeBuilder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_grantTokens().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static GetBeaconKeyOutput GetBeaconKeyOutput(
      Dafny.Aws.Cryptography.KeyStore.Types.GetBeaconKeyOutput dafnyValue) {
    GetBeaconKeyOutput.Builder nativeBuilder = GetBeaconKeyOutput.builder();
    nativeBuilder.beaconKeyIdentifier(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_beaconKeyIdentifier()));
    nativeBuilder.beaconKey(software.amazon.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_beaconKey()));
    return nativeBuilder.build();
  }

  public static CreateKeyStoreInput CreateKeyStoreInput(
      Dafny.Aws.Cryptography.KeyStore.Types.CreateKeyStoreInput dafnyValue) {
    CreateKeyStoreInput.Builder nativeBuilder = CreateKeyStoreInput.builder();
    return nativeBuilder.build();
  }

  public static GetBranchKeyVersionOutput GetBranchKeyVersionOutput(
      Dafny.Aws.Cryptography.KeyStore.Types.GetBranchKeyVersionOutput dafnyValue) {
    GetBranchKeyVersionOutput.Builder nativeBuilder = GetBranchKeyVersionOutput.builder();
    nativeBuilder.branchKeyVersion(software.amazon.dafny.conversion.ToNative.Simple.DafnyUtf8Bytes(dafnyValue.dtor_branchKeyVersion()));
    nativeBuilder.branchKey(software.amazon.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_branchKey()));
    return nativeBuilder.build();
  }

  public static GetBranchKeyVersionInput GetBranchKeyVersionInput(
      Dafny.Aws.Cryptography.KeyStore.Types.GetBranchKeyVersionInput dafnyValue) {
    GetBranchKeyVersionInput.Builder nativeBuilder = GetBranchKeyVersionInput.builder();
    nativeBuilder.branchKeyIdentifier(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_branchKeyIdentifier()));
    nativeBuilder.branchKeyVersion(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_branchKeyVersion()));
    if (dafnyValue.dtor_grantTokens().is_Some()) {
      nativeBuilder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_grantTokens().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static CreateKeyStoreOutput CreateKeyStoreOutput(
      Dafny.Aws.Cryptography.KeyStore.Types.CreateKeyStoreOutput dafnyValue) {
    CreateKeyStoreOutput.Builder nativeBuilder = CreateKeyStoreOutput.builder();
    nativeBuilder.tableArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_tableArn()));
    return nativeBuilder.build();
  }

  public static GetBeaconKeyInput GetBeaconKeyInput(
      Dafny.Aws.Cryptography.KeyStore.Types.GetBeaconKeyInput dafnyValue) {
    GetBeaconKeyInput.Builder nativeBuilder = GetBeaconKeyInput.builder();
    nativeBuilder.branchKeyIdentifier(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_branchKeyIdentifier()));
    if (dafnyValue.dtor_grantTokens().is_Some()) {
      nativeBuilder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_grantTokens().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static BranchKeyStatusResolutionInput BranchKeyStatusResolutionInput(
      Dafny.Aws.Cryptography.KeyStore.Types.BranchKeyStatusResolutionInput dafnyValue) {
    BranchKeyStatusResolutionInput.Builder nativeBuilder = BranchKeyStatusResolutionInput.builder();
    nativeBuilder.branchKeyIdentifier(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_branchKeyIdentifier()));
    if (dafnyValue.dtor_grantTokens().is_Some()) {
      nativeBuilder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_grantTokens().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static VersionKeyInput VersionKeyInput(
      Dafny.Aws.Cryptography.KeyStore.Types.VersionKeyInput dafnyValue) {
    VersionKeyInput.Builder nativeBuilder = VersionKeyInput.builder();
    nativeBuilder.branchKeyIdentifier(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_branchKeyIdentifier()));
    if (dafnyValue.dtor_grantTokens().is_Some()) {
      nativeBuilder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_grantTokens().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static CreateKeyOutput CreateKeyOutput(
      Dafny.Aws.Cryptography.KeyStore.Types.CreateKeyOutput dafnyValue) {
    CreateKeyOutput.Builder nativeBuilder = CreateKeyOutput.builder();
    nativeBuilder.branchKeyIdentifier(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_branchKeyIdentifier()));
    return nativeBuilder.build();
  }

  public static GetActiveBranchKeyOutput GetActiveBranchKeyOutput(
      Dafny.Aws.Cryptography.KeyStore.Types.GetActiveBranchKeyOutput dafnyValue) {
    GetActiveBranchKeyOutput.Builder nativeBuilder = GetActiveBranchKeyOutput.builder();
    nativeBuilder.branchKeyVersion(software.amazon.dafny.conversion.ToNative.Simple.DafnyUtf8Bytes(dafnyValue.dtor_branchKeyVersion()));
    nativeBuilder.branchKey(software.amazon.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_branchKey()));
    return nativeBuilder.build();
  }

  public static KeyStoreConfig KeyStoreConfig(
      Dafny.Aws.Cryptography.KeyStore.Types.KeyStoreConfig dafnyValue) {
    KeyStoreConfig.Builder nativeBuilder = KeyStoreConfig.builder();
    if (dafnyValue.dtor_id().is_Some()) {
      nativeBuilder.id(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_id().dtor_value()));
    }
    nativeBuilder.ddbTableName(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_ddbTableName()));
    nativeBuilder.kmsKeyArn(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_kmsKeyArn()));
    if (dafnyValue.dtor_ddbClient().is_Some()) {
      nativeBuilder.ddbClient(Dafny.Com.Amazonaws.Dynamodb.ToNative.DynamoDB_20120810(dafnyValue.dtor_ddbClient().dtor_value()));
    }
    if (dafnyValue.dtor_kmsClient().is_Some()) {
      nativeBuilder.kmsClient(Dafny.Com.Amazonaws.Kms.ToNative.TrentService(dafnyValue.dtor_kmsClient().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static GetActiveBranchKeyInput GetActiveBranchKeyInput(
      Dafny.Aws.Cryptography.KeyStore.Types.GetActiveBranchKeyInput dafnyValue) {
    GetActiveBranchKeyInput.Builder nativeBuilder = GetActiveBranchKeyInput.builder();
    nativeBuilder.branchKeyIdentifier(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_branchKeyIdentifier()));
    if (dafnyValue.dtor_grantTokens().is_Some()) {
      nativeBuilder.grantTokens(ToNative.GrantTokenList(dafnyValue.dtor_grantTokens().dtor_value()));
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
