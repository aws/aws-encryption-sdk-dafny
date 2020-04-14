using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Amazon;

using KMS = Amazon.KeyManagementService;
using IDString = Dafny.ISequence<char>;
using EncryptionContextMap = Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>;

namespace KMSUtils {

    public partial class __default {
        public static STL.Result<DefaultClient> GetDefaultClientExtern(STL.Option<IDString> region) {
            // TODO: Error handling
            DefaultClient kmsClient = new DefaultClient(region);
            return STL.Result<DefaultClient>.create_Success(kmsClient);
        }
    }

    public partial class DefaultClient : KMSClient {

        readonly private KMS.AmazonKeyManagementServiceClient client;

        public DefaultClient(STL.Option<IDString> region) {
            if (region.is_Some) {
                string regionString = DafnyFFI.StringFromDafnyString(((STL.Option_Some<IDString>)region).get);
                RegionEndpoint regionEndpoint = RegionEndpoint.GetBySystemName(regionString);
                this.client = new KMS.AmazonKeyManagementServiceClient(regionEndpoint);
            } else {
                this.client = new KMS.AmazonKeyManagementServiceClient();
            }
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
                return STL.Result<GenerateDataKeyResponse>.create_Failure(DafnyFFI.DafnyStringFromString(amzEx.ToString()));
            } catch (DecoderFallbackException decodeEx) {
                return STL.Result<GenerateDataKeyResponse>.create_Failure(DafnyFFI.DafnyStringFromString(decodeEx.ToString()));
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
                return STL.Result<EncryptResponse>.create_Failure(DafnyFFI.DafnyStringFromString(amzEx.ToString()));
            } catch (DecoderFallbackException decodeEx) {
                return STL.Result<EncryptResponse>.create_Failure(DafnyFFI.DafnyStringFromString(decodeEx.ToString()));
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
                return STL.Result<DecryptResponse>.create_Failure(DafnyFFI.DafnyStringFromString(amzEx.ToString()));
            } catch (DecoderFallbackException decodeEx) {
                return STL.Result<DecryptResponse>.create_Failure(DafnyFFI.DafnyStringFromString(decodeEx.ToString()));
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
