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
    stage('Dependencies') {
      steps {
        sh '''
          cd casper
          make deps -j3
        '''
      }
    }
    stage('Build') {
      steps {
        sh '''
          make build -j4
        '''
      }
    }
    stage('Test') {
      steps {
        sh '''
          make test -j8
        '''
      }
    }
  }
}

