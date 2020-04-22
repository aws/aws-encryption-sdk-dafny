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
        public static AWSKMSClientResult GetDefaultAWSKMSClientExtern(STL.Option<IDString> region) {
            AWSKMSServiceClientWrapper kmsClient = new AWSKMSServiceClientWrapper(region);
            return AWSKMSClientResult.create_Success(kmsClient);
        }
    }

    public class AWSKMSClientSupplierException : Exception
    {
        public AWSKMSClientSupplierException(string region)
            : base(String.Format("Unable to obtain client for region: {0}", region))
        {
        }
    }

    // DafnyAWSKMSClientSupplierWrapper is used to allow a Dafny AWSKMSClientSupplier to be used from a native context
    // Essentially, DafnyAWSKMSClientSupplierWrapper acts as a wrapper of a Dafny AWSKMSClientSupplier
    public partial class DafnyAWSKMSClientSupplierWrapper : AWSEncryptionSDK.AWSKMSClientSupplier {
        readonly private AWSKMSClientSupplier clientSupplier;

        public DafnyAWSKMSClientSupplierWrapper(AWSKMSClientSupplier clientSupplier) {
            this.clientSupplier = clientSupplier;
        }

        public KMS.AmazonKeyManagementServiceClient GetClient(string region) {
            // DafnyFFI.NullableToOption returns an optional of a given type, so we need to convert from an external
            // string to a Dafny string in the case where region != null. We cannot just
            // perform DafnyFFI.NullableToOption(region) directly
            STL.Option<IDString> dafnyRegion = DafnyFFI.NullableToOption<Dafny.ISequence<char>>(
                region == null ? null : DafnyFFI.DafnyStringFromString(region));
            AWSKMSClientResult clientResult = this.clientSupplier.GetClient(dafnyRegion);
            if (clientResult.is_Success) {
                return new DafnyAWSKMSClientWrapper(clientResult.dtor_value);
            } else {
                throw new AWSKMSClientSupplierException(region);
            }
        }
    }

    // DafnyAWSKMSClientSupplierWrapper is used to allow a Dafny AWSKMSClientSupplier to be used from a native context
    // Essentially, DafnyAWSKMSClientSupplierWrapper acts as a wrapper of a Dafny AWSKMSClientSupplier
    public partial class DafnyAWSKMSClientWrapper : KMS.IAmazonKeyManagementService {
        readonly private AWSKMSClient client;

        public DafnyAWSKMSClientWrapper(AWSKMSClient client) {
            this.client = client;
        }
    }

    // AWSKMSClientSupplierWrapper is used to allow a native AWSKMSClientSupplier to be used from a Dafny context
    // Essentially, AWSKMSClientSupplierWrapper acts a wrapper of AWSEncryptionSDK.AWSKMSClientSupplier
    public partial class AWSKMSClientSupplierWrapper : AWSKMSClientSupplier {
        readonly private AWSEncryptionSDK.AWSKMSClientSupplier clientSupplier;

        public AWSKMSClientSupplierWrapper(AWSEncryptionSDK.AWSKMSClientSupplier clientSupplier) {
            this.clientSupplier = clientSupplier;
        }

        public AWSKMSClientResult GetClient(STL.Option<IDString> region) {
            try {
                KMS.AmazonKeyManagementServiceClient client;
                if (region.is_None) {
                    client = clientSupplier.GetClient(null);
                } else {
                    string regionString = DafnyFFI.StringFromDafnyString(((STL.Option_Some<IDString>)region).get);
                    client = clientSupplier.GetClient(regionString);
                }
                return (client != null)
                    ? AWSKMSClientResult.create_Success(new AWSKMSServiceClientWrapper(client))
                    : AWSKMSClientResult.create_Failure(DafnyFFI.DafnyStringFromString("Unable to obtain AmazonKeyManagementServiceClient"));
            } catch(Exception e) {
                // By catching Exception, Dafny can handle failures accordingly, using a Failure Result
                return AWSKMSClientResult.create_Failure(DafnyFFI.DafnyStringFromString("Unable to obtain AmazonKeyManagementServiceClient"));
            }
        }
    }

    // AWSKMSServiceClientWrapper represents a default Dafny AWSKMSClient, which takes Dafny-based requests and converts them
    // into usable KMS.AmazonKeyManagementServiceClient calls that use the related ASync KMS.AmazonKeyManagementServiceClient
    // APIs (E.g. AWSKMSClient's GenerateDataKey method calls the KMS.AmazonKeyManagementServiceClient GenerateDataKeyAsync API)
    // Essentially, AWSKMSServiceClientWrapper acts as a wrapper of KMS.AmazonKeyManagementServiceClient
    public partial class AWSKMSServiceClientWrapper : AWSKMSClient {

        readonly private KMS.AmazonKeyManagementServiceClient client;

        // AWSKMSServiceClientWrapper can be created from an optional region when being invoked directly from Dafny
        public AWSKMSServiceClientWrapper(STL.Option<IDString> region) {
            if (region.is_Some) {
                string regionString = DafnyFFI.StringFromDafnyString(((STL.Option_Some<IDString>)region).get);
                RegionEndpoint regionEndpoint = RegionEndpoint.GetBySystemName(regionString);
                this.client = new KMS.AmazonKeyManagementServiceClient(regionEndpoint);
            } else {
                this.client = new KMS.AmazonKeyManagementServiceClient();
            }
        }

        // AWSKMSServiceClientWrapper can be created from an existing KMS.AmazonKeyManagementServiceClient when natively handled
        // by a customer AWSKMSClientSupplier. In this case, we assume the customer provided AWSKMSClientSupplier
        // determines the correct KMS.AmazonKeyManagementServiceClient to return, so this is converted to a Dafny
        // AWSKMSClient
        public AWSKMSServiceClientWrapper(KMS.AmazonKeyManagementServiceClient client) {
            this.client = client;
        }

        public STL.Result<GenerateDataKeyResponse> GenerateDataKey(GenerateDataKeyRequest request) {
            try {
                KMS.Model.GenerateDataKeyRequest kmsRequest = new KMS.Model.GenerateDataKeyRequest()
                {
                    EncryptionContext = EncryptionContextToString(request.encryptionContext),
                    GrantTokens = request.grantTokens.Elements.Select(element => DafnyFFI.StringFromDafnyString(element)).ToList(),
                    KeyId = DafnyFFI.StringFromDafnyString(request.keyID),
                    NumberOfBytes = request.numberOfBytes
                };
                KMS.Model.GenerateDataKeyResponse generateDataKeyResponse = this.client.GenerateDataKeyAsync(kmsRequest).Result;
                GenerateDataKeyResponse response = new GenerateDataKeyResponse(
                    DafnyFFI.SequenceFromMemoryStream(generateDataKeyResponse.CiphertextBlob),
                    generateDataKeyResponse.ContentLength,
                    (int)generateDataKeyResponse.HttpStatusCode,
                    DafnyFFI.DafnyStringFromString(generateDataKeyResponse.KeyId),
                    DafnyFFI.SequenceFromMemoryStream(generateDataKeyResponse.Plaintext),
                    ConvertMetaData(generateDataKeyResponse.ResponseMetadata));
                return STL.Result<GenerateDataKeyResponse>.create_Success(response);
            } catch (Amazon.Runtime.AmazonServiceException amzEx) {
                return STL.Result<GenerateDataKeyResponse>.create_Failure(DafnyFFI.DafnyStringFromString(amzEx.Message));
            } catch (Amazon.Runtime.Internal.HttpErrorResponseException httpEx) {
                return STL.Result<GenerateDataKeyResponse>.create_Failure(DafnyFFI.DafnyStringFromString(httpEx.Message));
            } catch (DecoderFallbackException decodeEx) {
                return STL.Result<GenerateDataKeyResponse>.create_Failure(DafnyFFI.DafnyStringFromString(decodeEx.Message));
            } catch (System.AggregateException aggregateEx) {
                return STL.Result<GenerateDataKeyResponse>.create_Failure(DafnyFFI.DafnyStringFromString(aggregateEx.Message));
            }
        }

        public STL.Result<EncryptResponse> Encrypt(EncryptRequest request) {
            try {
                KMS.Model.EncryptRequest kmsRequest = new KMS.Model.EncryptRequest()
                {
                    EncryptionContext = EncryptionContextToString(request.encryptionContext),
                    GrantTokens = request.grantTokens.Elements.Select(element => DafnyFFI.StringFromDafnyString(element)).ToList(),
                    KeyId = request.keyID.ToString(),
                    Plaintext = DafnyFFI.MemoryStreamFromSequence(request.plaintext)
                };
                KMS.Model.EncryptResponse encryptResponse = this.client.EncryptAsync(kmsRequest).Result;
                EncryptResponse response = new EncryptResponse(
                    DafnyFFI.SequenceFromMemoryStream(encryptResponse.CiphertextBlob),
                    encryptResponse.ContentLength,
                    (int)encryptResponse.HttpStatusCode,
                    DafnyFFI.DafnyStringFromString(encryptResponse.KeyId),
                    ConvertMetaData(encryptResponse.ResponseMetadata));
                return STL.Result<EncryptResponse>.create_Success(response);
            } catch (Amazon.Runtime.AmazonServiceException amzEx) {
                return STL.Result<EncryptResponse>.create_Failure(DafnyFFI.DafnyStringFromString(amzEx.Message));
            } catch (Amazon.Runtime.Internal.HttpErrorResponseException httpEx) {
                return STL.Result<EncryptResponse>.create_Failure(DafnyFFI.DafnyStringFromString(httpEx.Message));
            } catch (DecoderFallbackException decodeEx) {
                return STL.Result<EncryptResponse>.create_Failure(DafnyFFI.DafnyStringFromString(decodeEx.Message));
            } catch (System.AggregateException aggregateEx) {
                return STL.Result<EncryptResponse>.create_Failure(DafnyFFI.DafnyStringFromString(aggregateEx.Message));
            }
        }

        public STL.Result<DecryptResponse> Decrypt(DecryptRequest request) {
            try {
                KMS.Model.DecryptRequest kmsRequest = new KMS.Model.DecryptRequest()
                {
                    CiphertextBlob = DafnyFFI.MemoryStreamFromSequence(request.ciphertextBlob),
                    EncryptionContext = EncryptionContextToString(request.encryptionContext),
                    GrantTokens = request.grantTokens.Elements.Select(element => DafnyFFI.StringFromDafnyString(element)).ToList()
                };
                KMS.Model.DecryptResponse decryptResponse = this.client.DecryptAsync(kmsRequest).Result;
                DecryptResponse response = new DecryptResponse(
                    decryptResponse.ContentLength,
                    (int)decryptResponse.HttpStatusCode,
                    DafnyFFI.DafnyStringFromString(decryptResponse.KeyId),
                    DafnyFFI.SequenceFromMemoryStream(decryptResponse.Plaintext),
                    ConvertMetaData(decryptResponse.ResponseMetadata));
                return STL.Result<DecryptResponse>.create_Success(response);
            } catch (Amazon.Runtime.AmazonServiceException amzEx) {
                return STL.Result<DecryptResponse>.create_Failure(DafnyFFI.DafnyStringFromString(amzEx.Message));
            } catch (Amazon.Runtime.Internal.HttpErrorResponseException httpEx) {
                return STL.Result<DecryptResponse>.create_Failure(DafnyFFI.DafnyStringFromString(httpEx.Message));
            } catch (DecoderFallbackException decodeEx) {
                return STL.Result<DecryptResponse>.create_Failure(DafnyFFI.DafnyStringFromString(decodeEx.Message));
            } catch (System.AggregateException aggregateEx) {
                return STL.Result<DecryptResponse>.create_Failure(DafnyFFI.DafnyStringFromString(aggregateEx.Message));
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
            Dictionary<string, string> strDict = encContext.Items.Elements.ToDictionary(
                strKey => utf8.GetString(DafnyFFI.ByteArrayFromSequence(strKey._0)),
                strElm => utf8.GetString(DafnyFFI.ByteArrayFromSequence(strElm._1)));
            return strDict;
        }
    }
}
