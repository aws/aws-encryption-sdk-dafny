namespace aws.cryptography.materialProviders

use aws.polymorph#reference

use com.amazonaws.dynamodb#DynamoDB_20120810

///////////
// Clients

@reference(service: DynamoDB_20120810)
structure DdbClientReference {}
