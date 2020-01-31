pipeline {
  options {
    ansiColor('xterm')
  }
  agent { dockerfile { } }
  stages {
    stage('Init title') {
      when { changeRequest() }
      steps {
        script {
          currentBuild.displayName = "PR ${env.CHANGE_ID}: ${env.CHANGE_TITLE}"
        }
      }
    }
    stage('Build and Test') {
      parallel {
        stage('Dynamic - K') {
          stages {
            stage('Dependencies') {
              steps {
                sh '''
                  cd casper/k
                  make deps -j3
                '''
              }
            }
            stage('Build') {
              steps {
                sh '''
                  cd casper/k
                  make build -j4
                '''
              }
            }
          }
        }
        //stage('Static - Coq') {
        //  steps {
        //    sh '''
        //      cd casper/coq
        //      make
        //    '''
        //  }
        //}
      }
    }
  }
}

