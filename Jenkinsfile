@Library('StanUtils')
import org.stan.Utils

def utils = new org.stan.Utils()

pipeline {
    agent {
        dockerfile {
            dir 'docker'
            args '-u root --privileged' // TODO: set up a proper user in Dockerfile
        }
    }
    stages {
        stage('Kill previous builds') {
            when {
                not { branch 'develop' }
                not { branch 'master' }
            }
            steps {
                script {
                    utils.killOldBuilds()
                }
            }
        }
        stage("Build") {
            steps {
                sh 'eval $(opam env) && dune build @install'
            }
        }
    }
    post {
        always {
            script {utils.mailBuildResults()}
        }
    }

}
