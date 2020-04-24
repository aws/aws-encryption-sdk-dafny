// Add extern reference for a native AWS KMS service client
module {:extern "Amazon.KeyManagementService"} AmazonKeyManagementService {
  class {:extern "AmazonKeyManagementServiceClient"} AmazonKeyManagementServiceClient {}
}
