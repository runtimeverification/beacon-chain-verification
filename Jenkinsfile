pipeline {
  options { ansiColor('xterm') }
  agent {
    dockerfile {
      label 'docker'
      additionalBuildArgs '--build-arg K_COMMIT=$(cd deps/k && git rev-parse --short=7 HEAD) --build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
    }
  }
  stages {
    stage('Init title') {
      when { changeRequest() }
      steps { script { currentBuild.displayName = "PR ${env.CHANGE_ID}: ${env.CHANGE_TITLE}" } }
    }
    stage('Build and Test') {
      parallel {
        stage('Dynamic - K') {
          stages {
            stage('Build') { steps { sh 'cd dynamic && make build -j2' } }
            stage('Test')  { steps { sh 'cd dynamic && make test  -j4' } }
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

