using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;

using Amazon;

using KMS = Amazon.KeyManagementService;
using DString = Dafny.Sequence<char>;
using byteseq = Dafny.Sequence<byte>;
using EncryptionContext = Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>;

namespace KMSUtils {
    public partial class __default {
        //TODO: Issue #54
        public static Dictionary<String, String> EncryptionContextToString(EncryptionContext encContext) {
            UTF8Encoding utf8 = new UTF8Encoding(false, true);
            Dictionary<string, string> strDict = encContext.Elements.ToDictionary(
                    strKey => utf8.GetString(ConvertByteSeq(strKey._0)),
                    strElm => utf8.GetString(ConvertByteSeq(strElm._1))
                    );
            return strDict;
        }

        //TODO: Issue #54
        public static ResponseMetadata ConvertMetaData(Amazon.Runtime.ResponseMetadata rmd) {
            Dafny.Map<DString, DString> metadata = Dafny.Map<DString, DString>
                .FromCollection(rmd.Metadata.Select(
                            kvp => new Dafny.Pair<DString, DString>((DString.FromString(kvp.Key.ToString())), (DString.FromString(kvp.Value.ToString())))
                            ).ToList());
            DString requestID = DString.FromString(rmd.RequestId.ToString());
            return new ResponseMetadata(metadata, requestID);
        }
        public static byte[] ConvertByteSeq(byteseq bytes) {
            return (byte[])bytes.Elements.Clone();
        }
    }
    public partial class DefaultClientSupplier : ClientSupplier {
        public STL.Result<KMSClient> GetClient(STL.Option<DString> region) {
            if (region.is_Some) {
                DString neverUsed = DString.FromString("".ToString());
                return new STL.Result_Success<KMSClient>(new KMSClient(new KMS.AmazonKeyManagementServiceClient(RegionEndpoint.GetBySystemName(region.GetOrElse(neverUsed).ToString()))));
            } else {
                return new STL.Result_Failure<KMSClient>(DString.FromString("Client Supplier does not have default region.".ToString()));
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
            KMS.Model.GenerateDataKeyResponse response = this.client.GenerateDataKeyAsync(kmsRequest).Result;
            return new STL.Result_Success<GenerateDataKeyResponse>(new GenerateDataKeyResponse(
                    byteseq.FromArray(response.CiphertextBlob.ToArray()),
                    response.ContentLength,
                    (int)response.HttpStatusCode,
                    DString.FromString(response.KeyId.ToString()),
                    byteseq.FromArray(response.Plaintext.ToArray()),
                    __default.ConvertMetaData(response.ResponseMetadata)
                    ));
            } catch (Amazon.Runtime.AmazonServiceException amzEx) {
                return new STL.Result_Failure<GenerateDataKeyResponse>(DString.FromString(amzEx.ToString()));
            } catch (DecoderFallbackException decodeEx) {
                return new STL.Result_Failure<GenerateDataKeyResponse>(DString.FromString(decodeEx.ToString()));
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
                KMS.Model.EncryptResponse response = this.client.EncryptAsync(kmsRequest).Result;
                return new STL.Result_Success<EncryptResponse>(new EncryptResponse(
                            byteseq.FromArray(response.CiphertextBlob.ToArray()),
                            response.ContentLength,
                            (int)response.HttpStatusCode,
                            DString.FromString(response.KeyId.ToString()),
                            __default.ConvertMetaData(response.ResponseMetadata)
                            ));
            } catch (Amazon.Runtime.AmazonServiceException amzEx) {
                return new STL.Result_Failure<EncryptResponse>(DString.FromString(amzEx.ToString()));
            } catch (DecoderFallbackException decodeEx) {
                return new STL.Result_Failure<EncryptResponse>(DString.FromString(decodeEx.ToString()));
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
                KMS.Model.DecryptResponse response = this.client.DecryptAsync(kmsRequest).Result;
                return new STL.Result_Success<DecryptResponse>(new DecryptResponse(
                            response.ContentLength,
                            (int)response.HttpStatusCode,
                            DString.FromString(response.KeyId.ToString()),
                            byteseq.FromArray(response.Plaintext.ToArray()),
                            __default.ConvertMetaData(response.ResponseMetadata)
                            ));
            } catch (Amazon.Runtime.AmazonServiceException amzEx) {
                return new STL.Result_Failure<DecryptResponse>(DString.FromString(amzEx.ToString()));
            } catch (DecoderFallbackException decodeEx) {
                return new STL.Result_Failure<DecryptResponse>(DString.FromString(decodeEx.ToString()));
            }
        }
    }
}
