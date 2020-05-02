using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Amazon;

using KMS = Amazon.KeyManagementService;
using IDString = Dafny.ISequence<char>;
using EncryptionContextMap = Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>;

namespace KMSUtils {

    // ClientHelper represents a class containing Dafny KMS extern functionality
    public partial class ClientHelper {
        // GetDefaultAWSKMSClientExtern get a KMS service client from an optional region
        public static STL.Result<KMS.IAmazonKeyManagementService> GetDefaultAWSKMSServiceClientExtern(STL.Option<IDString> region) {
            KMS.AmazonKeyManagementServiceClient client;
            if (region.is_Some) {
                string regionString = DafnyFFI.StringFromDafnyString(((STL.Option_Some<IDString>)region).get);
                RegionEndpoint regionEndpoint = RegionEndpoint.GetBySystemName(regionString);
                client = new KMS.AmazonKeyManagementServiceClient(regionEndpoint);
            } else {
                client = new KMS.AmazonKeyManagementServiceClient();
            }
            return STL.Result<KMS.IAmazonKeyManagementService>.create_Success(client);
        }

        // GenerateDataKey calls the given KMS client's GenerateDataKeyAsync API
        public static STL.Result<GenerateDataKeyResponse> GenerateDataKey(KMS.IAmazonKeyManagementService client, GenerateDataKeyRequest request) {
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
                    generateDataKeyResponse.ContentLength,
                    (int)generateDataKeyResponse.HttpStatusCode,
                    DafnyFFI.DafnyStringFromString(generateDataKeyResponse.KeyId),
                    DafnyFFI.SequenceFromMemoryStream(generateDataKeyResponse.Plaintext),
                    ConvertMetaData(generateDataKeyResponse.ResponseMetadata));
                return STL.Result<GenerateDataKeyResponse>.create_Success(response);
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
        public static STL.Result<EncryptResponse> Encrypt(KMS.IAmazonKeyManagementService client, EncryptRequest request) {
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
                return STL.Result<EncryptResponse>.create_Success(response);
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
        public static STL.Result<DecryptResponse> Decrypt(KMS.IAmazonKeyManagementService client, DecryptRequest request) {
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
                return STL.Result<DecryptResponse>.create_Success(response);
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

        // AddCachingClientCallback adds a callback to the given client so that the client is added to the given cache on the first network call that confirms a valid endpoint.
        // The call does not need to return a successful response, it just needs to validate that the endpoint represents a valid AWS KMS endpoint in order for the client to be cached.
        // The client is cached as (key, value) = (region, client)
        public static void AddCachingClientCallback(KMS.IAmazonKeyManagementService client, STL.Option<IDString> region, CachingClientSupplierCache cache) {
            // Create a handler to cache the client after a network call is made a set of conditions is met
            Amazon.Runtime.ResponseEventHandler cacheClientEvent = ( _, e) =>
            {
                // Cast the response as a web service response
                // This allows us to check the response code
                Amazon.Runtime.WebServiceResponseEventArgs responseEvent = (Amazon.Runtime.WebServiceResponseEventArgs)e;

                // If there is no response, do not cache
                if (responseEvent == null || responseEvent.Response == null) {
                    return;
                }
                // Otherwise, we got a response, which means we can cache regardless of what that response was.
                // This is because errors from an AWS KMS contact still mean that the region is "live".
                // Therefore, the client can be cached because the request itself might be wrong, not necessarily the client.

                // Double check the client does not already exist.
                // AddClient overrides the existing client if it's there anyways.
                STL.Option<KMS.IAmazonKeyManagementService> alreadyCachedClient = cache.LookupClient(region);
                if (alreadyCachedClient.is_None) {
                    cache.AddClient(region, client);
                }
                return;
            };
            // A cast needs to be performed so that we can properly use AfterResponseEvent, which is not part of the interface
            Amazon.Runtime.AmazonServiceClient castClient = (Amazon.Runtime.AmazonServiceClient)client;

            // Add the ResponseEventHandler to the AfterResponseEvent handlers
            // so the handler runs after a network call is made and a response is obtained
            castClient.AfterResponseEvent += cacheClientEvent;
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
            Dictionary<string, string> strDict = encContext.Items.Elements.ToDictionary(
                strKey => utf8.GetString(DafnyFFI.ByteArrayFromSequence(strKey._0)),
                strElm => utf8.GetString(DafnyFFI.ByteArrayFromSequence(strElm._1)));
            return strDict;
        }
    }

    // DafnyAWSKMSClientSupplierAsNative is used to allow a DafnyAWSKMSClientSupplier to be used from a native context (implement AWSKMSClientSupplier)
    // Essentially, DafnyAWSKMSClientSupplierAsNative acts as a wrapper of a DafnyAWSKMSClientSupplier
    public partial class DafnyAWSKMSClientSupplierAsNative : AWSEncryptionSDK.AWSKMSClientSupplier {
        readonly private DafnyAWSKMSClientSupplier clientSupplier;

        public DafnyAWSKMSClientSupplierAsNative(DafnyAWSKMSClientSupplier clientSupplier) {
            this.clientSupplier = clientSupplier;
        }

        public KMS.IAmazonKeyManagementService GetClient(string region) {
            // DafnyFFI.NullableToOption returns an optional of a given type, so we need to convert from an external string to a Dafny string in the case where region != null.
            // We cannot just perform DafnyFFI.NullableToOption(region) directly
            STL.Option<IDString> dafnyRegion = DafnyFFI.NullableToOption<Dafny.ISequence<char>>(
                region == null ? null : DafnyFFI.DafnyStringFromString(region));
            STL.Result<KMS.IAmazonKeyManagementService> clientResult = this.clientSupplier.GetClient(dafnyRegion);
            if (clientResult.is_Success) {
                return clientResult.dtor_value;
            } else {
                throw new AWSEncryptionSDK.AWSKMSClientSupplierException(DafnyFFI.StringFromDafnyString(clientResult.dtor_error));
            }
        }
    }

    // AWSKMSClientSupplierAsDafny is used to allow a native AWSKMSClientSupplier to be used from a Dafny context (implement DafnyAWSKMSClientSupplier)
    // Essentially, AWSKMSClientSupplierAsDafny acts a wrapper of AWSEncryptionSDK.AWSKMSClientSupplier
    public partial class AWSKMSClientSupplierAsDafny : DafnyAWSKMSClientSupplier {
        readonly private AWSEncryptionSDK.AWSKMSClientSupplier clientSupplier;

        public AWSKMSClientSupplierAsDafny(AWSEncryptionSDK.AWSKMSClientSupplier clientSupplier) {
            this.clientSupplier = clientSupplier;
        }

        public STL.Result<KMS.IAmazonKeyManagementService> GetClient(STL.Option<IDString> region) {
            try {
                KMS.IAmazonKeyManagementService client;
                if (region.is_None) {
                    client = clientSupplier.GetClient(null);
                } else {
                    string regionString = DafnyFFI.StringFromDafnyString(((STL.Option_Some<IDString>)region).get);
                    client = clientSupplier.GetClient(regionString);
                }
                return (client != null)
                    ? STL.Result<KMS.IAmazonKeyManagementService>.create_Success(client)
                    : DafnyFFI.CreateFailure<KMS.IAmazonKeyManagementService>(
                        String.Format("Unable to obtain AmazonKeyManagementServiceClient for region: {0}", region));
            } catch(Exception e) {
                // By catching Exception, Dafny can handle failures accordingly, using a Failure Result
                return DafnyFFI.CreateFailure<KMS.IAmazonKeyManagementService>(e.Message);
            }
        }
    }
}
