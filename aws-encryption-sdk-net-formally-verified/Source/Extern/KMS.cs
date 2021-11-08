// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Amazon;

using Wrappers_Compile;
using KMS = Amazon.KeyManagementService;
using IDString = Dafny.ISequence<char>;
using EncryptionContextMap = Dafny.IMap<Dafny.ISequence<byte>, Dafny.ISequence<byte>>;

namespace KMSUtils {

    // ClientHelper represents a class containing Dafny KMS extern functionality
    public partial class ClientHelper {
        // GetDefaultAWSKMSClientExtern get a KMS service client from an optional region
        public static Result<KMS.IAmazonKeyManagementService, IDString> GetDefaultAWSKMSServiceClientExtern(Option<IDString> region) {
            KMS.AmazonKeyManagementServiceClient client;
            if (region.is_Some) {
                string regionString = DafnyFFI.StringFromDafnyString(((Option_Some<IDString>)region).value);
                RegionEndpoint regionEndpoint = RegionEndpoint.GetBySystemName(regionString);
                client = new KMS.AmazonKeyManagementServiceClient(regionEndpoint);
            } else {
                client = new KMS.AmazonKeyManagementServiceClient();
            }
            return Result<KMS.IAmazonKeyManagementService, IDString>.create_Success(client);
        }

        // GenerateDataKey calls the given KMS client's GenerateDataKeyAsync API
        public static Result<GenerateDataKeyResponse, IDString> GenerateDataKey(KMS.IAmazonKeyManagementService client, GenerateDataKeyRequest request) {
            if (client == null) {
                return DafnyFFI.CreateFailure<GenerateDataKeyResponse>("Null AmazonKeyManagementServiceClient provided");
            }
            if (request == null) {
                return DafnyFFI.CreateFailure<GenerateDataKeyResponse>("Null request provided");
            }
            try {
                KMS.Model.GenerateDataKeyRequest kmsRequest = new KMS.Model.GenerateDataKeyRequest()
                {
                    EncryptionContext = EncryptionContextToString(request.encryptionContext),
                    GrantTokens = request.grantTokens.Elements.Select(element => DafnyFFI.StringFromDafnyString(element)).ToList(),
                    KeyId = DafnyFFI.StringFromDafnyString(request.keyID),
                    NumberOfBytes = request.numberOfBytes
                };
                KMS.Model.GenerateDataKeyResponse generateDataKeyResponse = client.GenerateDataKeyAsync(kmsRequest).Result;
                GenerateDataKeyResponse response = new GenerateDataKeyResponse(
                    DafnyFFI.SequenceFromMemoryStream(generateDataKeyResponse.CiphertextBlob),
                    DafnyFFI.DafnyStringFromString(generateDataKeyResponse.KeyId),
                    DafnyFFI.SequenceFromMemoryStream(generateDataKeyResponse.Plaintext));
                return Result<GenerateDataKeyResponse, IDString>.create_Success(response);
            } catch (Amazon.Runtime.AmazonServiceException amzEx) {
                return DafnyFFI.CreateFailure<GenerateDataKeyResponse>(amzEx.Message);
            } catch (Amazon.Runtime.Internal.HttpErrorResponseException httpEx) {
                return DafnyFFI.CreateFailure<GenerateDataKeyResponse>(httpEx.Message);
            } catch (DecoderFallbackException decodeEx) {
                return DafnyFFI.CreateFailure<GenerateDataKeyResponse>(decodeEx.Message);
            } catch (System.AggregateException aggregateEx) {
                return DafnyFFI.CreateFailure<GenerateDataKeyResponse>(aggregateEx.Message);
            }
        }

        // Encrypt calls the given KMS client's EncryptAsync API
        public static Result<EncryptResponse, IDString> Encrypt(KMS.IAmazonKeyManagementService client, EncryptRequest request) {
            if (client == null) {
                return DafnyFFI.CreateFailure<EncryptResponse>("Null AmazonKeyManagementServiceClient provided");
            }
            if (request == null) {
                return DafnyFFI.CreateFailure<EncryptResponse>("Null request provided");
            }
            try {
                KMS.Model.EncryptRequest kmsRequest = new KMS.Model.EncryptRequest()
                {
                    EncryptionContext = EncryptionContextToString(request.encryptionContext),
                    GrantTokens = request.grantTokens.Elements.Select(element => DafnyFFI.StringFromDafnyString(element)).ToList(),
                    KeyId = request.keyID.ToString(),
                    Plaintext = DafnyFFI.MemoryStreamFromSequence(request.plaintext)
                };
                KMS.Model.EncryptResponse encryptResponse = client.EncryptAsync(kmsRequest).Result;
                EncryptResponse response = new EncryptResponse(
                    DafnyFFI.SequenceFromMemoryStream(encryptResponse.CiphertextBlob),
                    encryptResponse.ContentLength,
                    (int)encryptResponse.HttpStatusCode,
                    DafnyFFI.DafnyStringFromString(encryptResponse.KeyId),
                    ConvertMetaData(encryptResponse.ResponseMetadata));
                return Result<EncryptResponse, IDString>.create_Success(response);
            } catch (Amazon.Runtime.AmazonServiceException amzEx) {
                return DafnyFFI.CreateFailure<EncryptResponse>(amzEx.Message);
            } catch (Amazon.Runtime.Internal.HttpErrorResponseException httpEx) {
                return DafnyFFI.CreateFailure<EncryptResponse>(httpEx.Message);
            } catch (DecoderFallbackException decodeEx) {
                return DafnyFFI.CreateFailure<EncryptResponse>(decodeEx.Message);
            } catch (System.AggregateException aggregateEx) {
                return DafnyFFI.CreateFailure<EncryptResponse>(aggregateEx.Message);
            }
        }

        // Decrypt calls the given KMS client's DecryptAsync API
        public static Result<DecryptResponse, IDString> Decrypt(KMS.IAmazonKeyManagementService client, DecryptRequest request) {
            if (client == null) {
                return DafnyFFI.CreateFailure<DecryptResponse>("Null AmazonKeyManagementServiceClient provided");
            }
            if (request == null) {
                return DafnyFFI.CreateFailure<DecryptResponse>("Null request provided");
            }
            try {
                KMS.Model.DecryptRequest kmsRequest = new KMS.Model.DecryptRequest()
                {
                    CiphertextBlob = DafnyFFI.MemoryStreamFromSequence(request.ciphertextBlob),
                    EncryptionContext = EncryptionContextToString(request.encryptionContext),
                    GrantTokens = request.grantTokens.Elements.Select(element => DafnyFFI.StringFromDafnyString(element)).ToList()
                };
                KMS.Model.DecryptResponse decryptResponse = client.DecryptAsync(kmsRequest).Result;
                DecryptResponse response = new DecryptResponse(
                    decryptResponse.ContentLength,
                    (int)decryptResponse.HttpStatusCode,
                    DafnyFFI.DafnyStringFromString(decryptResponse.KeyId),
                    DafnyFFI.SequenceFromMemoryStream(decryptResponse.Plaintext),
                    ConvertMetaData(decryptResponse.ResponseMetadata));
                return Result<DecryptResponse, IDString>.create_Success(response);
            } catch (Amazon.Runtime.AmazonServiceException amzEx) {
                return DafnyFFI.CreateFailure<DecryptResponse>(amzEx.Message);
            } catch (Amazon.Runtime.Internal.HttpErrorResponseException httpEx) {
                return DafnyFFI.CreateFailure<DecryptResponse>(httpEx.Message);
            } catch (DecoderFallbackException decodeEx) {
                return DafnyFFI.CreateFailure<DecryptResponse>(decodeEx.Message);
            } catch (System.AggregateException aggregateEx) {
                return DafnyFFI.CreateFailure<DecryptResponse>(aggregateEx.Message);
            }
        }

        private static ResponseMetadata ConvertMetaData(Amazon.Runtime.ResponseMetadata rmd) {
            Dafny.Map<IDString, IDString> metadata = Dafny.Map<IDString, IDString>.FromCollection(
                rmd.Metadata.Select(
                    kvp => new Dafny.Pair<IDString, IDString>(DafnyFFI.DafnyStringFromString(kvp.Key), DafnyFFI.DafnyStringFromString(kvp.Value)))
                .ToList());
            IDString requestID = DafnyFFI.DafnyStringFromString(rmd.RequestId);
            return new ResponseMetadata(metadata, requestID);
        }

        private static Dictionary<String, String> EncryptionContextToString(EncryptionContextMap encContext) {
            UTF8Encoding utf8 = new UTF8Encoding(false, true);
            Dictionary<string, string> strDict = encContext.ItemEnumerable.ToDictionary(
                item => utf8.GetString(DafnyFFI.ByteArrayFromSequence(item.Car)),
                item => utf8.GetString(DafnyFFI.ByteArrayFromSequence(item.Cdr)));
            return strDict;
        }
    }
}
