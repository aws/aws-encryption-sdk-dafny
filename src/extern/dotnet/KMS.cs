using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;

using Amazon;

using KMS = Amazon.KeyManagementService;
using DString = Dafny.Sequence<char>;
using ArrayDString = Dafny.ArraySequence<char>;
using byteseq = Dafny.Sequence<byte>;
using Arraybyteseq = Dafny.ArraySequence<byte>;
using EncryptionContext = Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>;
using ArrayEncryptionContext = Dafny.ArraySequence<_System.Tuple2<Dafny.ArraySequence<byte>,Dafny.ArraySequence<byte>>>;

namespace KMSUtils {
    public partial class __default {
        public static KMSClient GetClient(DString region) {
            return new KMSClient(new KMS.AmazonKeyManagementServiceClient(RegionEndpoint.GetBySystemName(region.ToString())));
        }
        //TODO: #54
        public static Dictionary<String, String> EncryptionContextToString(EncryptionContext encContext) {
            UTF8Encoding utf8 = new UTF8Encoding(false, true);
            Dictionary<string, string> strDict = encContext.Elements.ToDictionary(
                    strKey => utf8.GetString((byte[])strKey._0.Elements.Clone()),
                    strElm => utf8.GetString((byte[])strElm._1.Elements.Clone())
                    );
            return strDict;
        }

        //TODO: #54
        public static ResponseMetadata ConvertMetaData(Amazon.Runtime.ResponseMetadata rmd) {
            Dafny.Map<DString, DString> metadata = Dafny.Map<DString, DString>
                .FromCollection(rmd.Metadata.Select(
                            kvp => new Dafny.Pair<DString, DString>((DString)(new ArrayDString(kvp.Key.ToCharArray())), (DString)(new ArrayDString(kvp.Value.ToCharArray())))
                            ).ToList());
            DString requestID = new ArrayDString(rmd.RequestId.ToCharArray());
            return new ResponseMetadata(metadata, requestID);
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
            KMS.Model.GenerateDataKeyResponse response = this.client.GenerateDataKey(kmsRequest);
            return new STL.Result_Success<GenerateDataKeyResponse>(new GenerateDataKeyResponse(
                    new Arraybyteseq(response.CiphertextBlob.ToArray()),
                    response.ContentLength,
                    (int)response.HttpStatusCode,
                    new ArrayDString(response.KeyId.ToCharArray()),
                    new Arraybyteseq(response.Plaintext.ToArray()),
                    __default.ConvertMetaData(response.ResponseMetadata)
                    ));
            } catch (System.Exception exception) {
                return new STL.Result_Failure<GenerateDataKeyResponse>(new ArrayDString(exception.ToString().ToCharArray()));
            }
        }

        public STL.Result<EncryptResponse> Encrypt(EncryptRequest request) {
            try {
                KMS.Model.EncryptRequest kmsRequest = new KMS.Model.EncryptRequest()
                {
                    EncryptionContext = __default.EncryptionContextToString(request.encryptionContext),
                    GrantTokens = request.grantTokens.Elements.Select(element => element.ToString()).ToList(),
                    KeyId = request.keyID.ToString(),
                    Plaintext = new MemoryStream((byte[])request.plaintext.Elements.Clone())
                };
                KMS.Model.EncryptResponse response = this.client.Encrypt(kmsRequest);
                return new STL.Result_Success<EncryptResponse>(new EncryptResponse(
                            new Arraybyteseq(response.CiphertextBlob.ToArray()),
                            response.ContentLength,
                            (int)response.HttpStatusCode,
                            new ArrayDString(response.KeyId.ToCharArray()),
                            __default.ConvertMetaData(response.ResponseMetadata)
                            ));
            } catch (System.Exception exception) {
                return new STL.Result_Failure<EncryptResponse>(new ArrayDString(exception.ToString().ToCharArray()));
            }
        }

        public STL.Result<DecryptResponse> Decrypt(DecryptRequest request) {
            try {
                KMS.Model.DecryptRequest kmsRequest = new KMS.Model.DecryptRequest()
                {
                    CiphertextBlob = new MemoryStream((byte[])request.ciphertextBlob.Elements.Clone()),
                    EncryptionContext = __default.EncryptionContextToString(request.encryptionContext),
                    GrantTokens = request.grantTokens.Elements.Select(element => element.ToString()).ToList(),
                };
                KMS.Model.DecryptResponse response = this.client.Decrypt(kmsRequest);
                return new STL.Result_Success<DecryptResponse>(new DecryptResponse(
                            response.ContentLength,
                            (int)response.HttpStatusCode,
                            new ArrayDString(response.KeyId.ToCharArray()),
                            new Arraybyteseq(response.Plaintext.ToArray()),
                            __default.ConvertMetaData(response.ResponseMetadata)
                            ));
            } catch (System.Exception exception) {
                return new STL.Result_Failure<DecryptResponse>(new ArrayDString(exception.ToString().ToCharArray()));
            }
        }
    }
}
