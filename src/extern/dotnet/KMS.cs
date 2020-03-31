using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;

using Amazon;

using KMS = Amazon.KeyManagementService;
using IDString = Dafny.ISequence<char>;
using DString = Dafny.Sequence<char>;
using ibyteseq = Dafny.ISequence<byte>;
using byteseq = Dafny.Sequence<byte>;
using EncryptionContextT = Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>;

namespace KMSUtils {
    public partial class __default {
        //TODO: Issue #54
        public static Dictionary<String, String> EncryptionContextToString(EncryptionContextT encContext) {
            UTF8Encoding utf8 = new UTF8Encoding(false, true);
            Dictionary<string, string> strDict = encContext.Items.Elements.ToDictionary(
                    strKey => utf8.GetString(ConvertByteSeq(strKey._0)),
                    strElm => utf8.GetString(ConvertByteSeq(strElm._1))
                    );
            return strDict;
        }

        //TODO: Issue #54
        public static ResponseMetadata ConvertMetaData(Amazon.Runtime.ResponseMetadata rmd) {
            Dafny.Map<IDString, IDString> metadata = Dafny.Map<IDString, IDString>
                .FromCollection(rmd.Metadata.Select(
                            kvp => new Dafny.Pair<IDString, IDString>((DString.FromString(kvp.Key.ToString())), (DString.FromString(kvp.Value.ToString())))
                            ).ToList());
            IDString requestID = DString.FromString(rmd.RequestId.ToString());
            return new ResponseMetadata(metadata, requestID);
        }
        public static byte[] ConvertByteSeq(ibyteseq bytes) {
            return (byte[])bytes.Elements.Clone();
        }
    }
    public partial class DefaultClientSupplier : ClientSupplier {
        public STL.Result<KMSClient> GetClient(STL.Option<IDString> region) {
            if (region.is_Some) {
                string regionString = ((STL.Option_Some<IDString>) region).get.ToString();
                RegionEndpoint regionEndpoint = RegionEndpoint.GetBySystemName(regionString);
                KMS.AmazonKeyManagementServiceClient amazonKeyManagementServiceClient = new KMS.AmazonKeyManagementServiceClient(regionEndpoint);
                KMSClient kmsClient = new KMSClient(amazonKeyManagementServiceClient);
                return STL.Result<KMSClient>.create_Success(kmsClient);
            } else {
                return STL.Result<KMSClient>.create_Failure(DString.FromString("Client Supplier does not have default region."));
            }
        }
    }
    public partial class KMSClient {

        readonly private KMS.AmazonKeyManagementServiceClient client;

        public KMSClient(KMS.AmazonKeyManagementServiceClient client) {
            this.client = client;
        }

        public STL.Result<GenerateDataKeyResponse> GenerateDataKey(GenerateDataKeyRequest request) {
            try {
            KMS.Model.GenerateDataKeyRequest kmsRequest = new KMS.Model.GenerateDataKeyRequest()
            {
                EncryptionContext = __default.EncryptionContextToString(request.encryptionContext),
                GrantTokens = request.grantTokens.Elements.Select(element => element.ToString()).ToList(),
                KeyId = request.keyID.ToString(),
                NumberOfBytes = request.numberOfBytes
            };
            KMS.Model.GenerateDataKeyResponse generateDataKeyResponse = this.client.GenerateDataKeyAsync(kmsRequest).Result;
            GenerateDataKeyResponse response = new GenerateDataKeyResponse(
                byteseq.FromArray(generateDataKeyResponse.CiphertextBlob.ToArray()),
                generateDataKeyResponse.ContentLength,
                (int) generateDataKeyResponse.HttpStatusCode,
                DString.FromString(generateDataKeyResponse.KeyId.ToString()),
                byteseq.FromArray(generateDataKeyResponse.Plaintext.ToArray()),
                __default.ConvertMetaData(generateDataKeyResponse.ResponseMetadata));
            return STL.Result<GenerateDataKeyResponse>.create_Success(response);
            } catch (Amazon.Runtime.AmazonServiceException amzEx) {
                return STL.Result<GenerateDataKeyResponse>.create_Failure(DString.FromString(amzEx.ToString()));
            } catch (DecoderFallbackException decodeEx) {
                return STL.Result<GenerateDataKeyResponse>.create_Failure(DString.FromString(decodeEx.ToString()));
            }
        }

        public STL.Result<EncryptResponse> Encrypt(EncryptRequest request) {
            try {
                KMS.Model.EncryptRequest kmsRequest = new KMS.Model.EncryptRequest()
                {
                    EncryptionContext = __default.EncryptionContextToString(request.encryptionContext),
                    GrantTokens = request.grantTokens.Elements.Select(element => element.ToString()).ToList(),
                    KeyId = request.keyID.ToString(),
                    Plaintext = new MemoryStream(__default.ConvertByteSeq(request.plaintext))
                };
                KMS.Model.EncryptResponse encryptResponse = this.client.EncryptAsync(kmsRequest).Result;
                EncryptResponse response = new EncryptResponse(
                    byteseq.FromArray(encryptResponse.CiphertextBlob.ToArray()),
                    encryptResponse.ContentLength,
                    (int) encryptResponse.HttpStatusCode,
                    DString.FromString(encryptResponse.KeyId.ToString()),
                    __default.ConvertMetaData(encryptResponse.ResponseMetadata));
                return STL.Result<EncryptResponse>.create_Success(response);
            } catch (Amazon.Runtime.AmazonServiceException amzEx) {
                return STL.Result<EncryptResponse>.create_Failure(DString.FromString(amzEx.ToString()));
            } catch (DecoderFallbackException decodeEx) {
                return STL.Result<EncryptResponse>.create_Failure(DString.FromString(decodeEx.ToString()));
            }
        }

        public STL.Result<DecryptResponse> Decrypt(DecryptRequest request) {
            try {
                KMS.Model.DecryptRequest kmsRequest = new KMS.Model.DecryptRequest()
                {
                    CiphertextBlob = new MemoryStream(__default.ConvertByteSeq(request.ciphertextBlob)),
                    EncryptionContext = __default.EncryptionContextToString(request.encryptionContext),
                    GrantTokens = request.grantTokens.Elements.Select(element => element.ToString()).ToList(),
                };
                KMS.Model.DecryptResponse decryptResponse = this.client.DecryptAsync(kmsRequest).Result;
                DecryptResponse response = new DecryptResponse(
                    decryptResponse.ContentLength,
                    (int) decryptResponse.HttpStatusCode,
                    DString.FromString(decryptResponse.KeyId.ToString()),
                    byteseq.FromArray(decryptResponse.Plaintext.ToArray()),
                    __default.ConvertMetaData(decryptResponse.ResponseMetadata));
                return STL.Result<DecryptResponse>.create_Success(response);
            } catch (Amazon.Runtime.AmazonServiceException amzEx) {
                return STL.Result<DecryptResponse>.create_Failure(DString.FromString(amzEx.ToString()));
            } catch (DecoderFallbackException decodeEx) {
                return STL.Result<DecryptResponse>.create_Failure(DString.FromString(decodeEx.ToString()));
            }
        }
    }
}
