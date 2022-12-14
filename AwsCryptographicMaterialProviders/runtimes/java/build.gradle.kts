import java.net.URI
import javax.annotation.Nullable

plugins {
    `java-library`
    `maven-publish`
}

group = "software.amazon.cryptography"
version = "1.0-SNAPSHOT"
description = "AwsCryptographicMaterialProviders"

java {
    toolchain.languageVersion.set(JavaLanguageVersion.of(8))
    sourceSets["main"].java {
        srcDir("src/main/java")
        srcDir("src/main/dafny-generated")
        srcDir("src/main/smithy-generated")
    }
    sourceSets["test"].java {
        srcDir("src/test/dafny-generated")
    }
}

var caUrl: URI? = null
@Nullable
val caUrlStr: String? = System.getenv("CODEARTIFACT_URL_JAVA_CONVERSION")
if (!caUrlStr.isNullOrBlank()) {
    caUrl = URI.create(caUrlStr)
}

var caPassword: String? = null
@Nullable
val caPasswordString: String? = System.getenv("CODEARTIFACT_AUTH_TOKEN")
if (!caPasswordString.isNullOrBlank()) {
    caPassword = caPasswordString
}

repositories {
    mavenCentral()
    mavenLocal()
    if (caUrl != null && caPassword != null) {
        maven {
            name = "CodeArtifact"
            url = caUrl!!
            credentials {
                username = "aws"
                password = caPassword!!
            }
        }
    }
}

dependencies {
    implementation("dafny.lang:DafnyRuntime:3.10.0")
    implementation("software.amazon.dafny:conversion:1.0-SNAPSHOT")
    implementation("software.amazon.cryptography:StandardLibrary:1.0-SNAPSHOT")
    implementation("software.amazon.cryptography:AwsCryptographyPrimitives:1.0-SNAPSHOT")
    implementation("software.amazon.cryptography:ComAmazonawsKms:1.0-SNAPSHOT")
    implementation("com.amazonaws:aws-java-sdk:1.12.347")
    /*implementation("software.amazon.cryptography:ComAmazonawsDynamodb:1.0-SNAPSHOT")*/
}

publishing {
    publications.create<MavenPublication>("maven") {
        groupId = "software.amazon.cryptography"
        artifactId = "AwsCryptographicMaterialProviders"
        from(components["java"])
    }
    repositories { mavenLocal() }
}

tasks.withType<JavaCompile>() {
    options.encoding = "UTF-8"
}

tasks {
    register("runTests", JavaExec::class.java) {
        mainClass.set("AwsCryptographicMaterialProvidersTests")
        classpath = sourceSets["test"].runtimeClasspath
    }
}
