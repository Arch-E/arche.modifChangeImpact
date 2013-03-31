/*
 * ArchE
 * Copyright (c) 2012 Carnegie Mellon University.
 * All Rights Reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the following acknowledgments and disclaimers.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 * this list of conditions and the following disclaimer in the documentation
 * and/or other materials provided with the distribution.
 *
 * 3. All advertising materials for third-party software mentioning features or
 * use of this software must display the following disclaimer:
 *
 * “Neither Carnegie Mellon University nor its Software Engineering Institute
 * have reviewed or endorsed this software”
 *
 * 4. The names “Carnegie Mellon University,” and/or “Software Engineering
 * Institute" shall not be used to endorse or promote products derived from
 * this software without prior written permission. For written permission,
 * please contact permission@sei.cmu.edu.
 *
 * 5. Redistributions of any form whatsoever must retain the following
 * acknowledgment:
 *
 * Copyright 2012 Carnegie Mellon University.
 *
 * This material is based upon work funded and supported by the United States
 * Department of Defense under Contract No. FA8721-05-C-0003 with Carnegie
 * Mellon University for the operation of the Software Engineering Institute, a
 * federally funded research and development center.
 *
 * NO WARRANTY
 *
 * THIS CARNEGIE MELLON UNIVERSITY AND SOFTWARE ENGINEERING INSTITUTE MATERIAL
 * IS FURNISHED ON AN “AS-IS” BASIS. CARNEGIE MELLON UNIVERSITY MAKES NO
 * WARRANTIES OF ANY KIND, EITHER EXPRESSED OR IMPLIED, AS TO ANY MATTER
 * INCLUDING, BUT NOT LIMITED TO, WARRANTY OF FITNESS FOR PURPOSE OR
 * MERCHANTABILITY, EXCLUSIVITY, OR RESULTS OBTAINED FROM USE OF THE MATERIAL.
 * CARNEGIE MELLON UNIVERSITY DOES NOT MAKE ANY WARRANTY OF ANY KIND WITH
 * RESPECT TO FREEDOM FROM PATENT, TRADEMARK, OR COPYRIGHT INFRINGEMENT.
 */

package arche.modifChangeImpact.hibernate.vo;

/**
 * VO class that represents a 6-part quality-attribute scenario 
 * (as defined in ArchE). 
 * <p>
 * These objects are created/manipulated by the ArchE core, so that each 
 * external reasoning framework should only restore scenarios from the database. 
 * <p>
 * This is a core concept that should not be extended by reasoning frameworks
 * 
 * @author Hyunwoo Kim
 */

import edu.cmu.sei.arche.external.data.ArchEScenario;

public class ArchEScenarioVO implements ArchEScenario {

	private static final long serialVersionUID = 1L;
	
	private Integer uid;
	private int versionNumber;
	private String factId;
	private ArchEVersionVO version;
	private String id; // TODO: To be removed
	private String state;
	private String reasoningFramework;

	// The different parts of the scenario
	private String description;
	private String quality;
	private String stimulusText;
	private String stimulusType;
	private String stimulusUnit;
	private Double stimulusValue;
	private String sourceText;
	private String sourceType;
	private String sourceUnit;
	private Double sourceValue;
	private String artifactText;
	private String artifactType;
	private String artifactUnit;
	private Double artifactValue;
	private String environmentText;
	private String environmentType;
	private String environmentUnit;
	private Double environmentValue;
	private String responseText;
	private String responseType;
	private String responseUnit;
	private Double responseValue;
	private String measureText;
	private String measureType;
	private String measureUnit;
	private Double measureValue;

	public ArchEScenarioVO() {
	}

	public Integer getUid() {
		return this.uid;
	}

	public void setUid(Integer uid) {
		this.uid = uid;
	}

	public int getVersionNumber() {
		return this.versionNumber;
	}

	public void setVersionNumber(int versionNumber) {
		this.versionNumber = versionNumber;
	}

	public String getFactId() {
		return this.factId;
	}

	public void setFactId(String factId) {
		this.factId = factId;
	}

	public ArchEVersionVO getVersion() {
		return this.version;
	}

	public void setVersion(ArchEVersionVO version) {
		this.version = version;
		this.versionNumber = version.getId();
	}

	public String getId() {
		return this.id;
	}

	public void setId(String id) {
		this.id = id;
	}

	public String getDescription() {
		return this.description;
	}

	public void setDescription(String description) {
		this.description = description;
	}

	public String getQuality() {
		return this.quality;
	}

	public void setQuality(String quality) {
		this.quality = quality;
	}

	public String getStimulusText() {
		return this.stimulusText;
	}

	public void setStimulusText(String stimulusText) {
		this.stimulusText = stimulusText;
	}

	public String getStimulusType() {
		return this.stimulusType;
	}

	public void setStimulusType(String stimulusType) {
		this.stimulusType = stimulusType;
	}

	public String getStimulusUnit() {
		return this.stimulusUnit;
	}

	public void setStimulusUnit(String stimulusUnit) {
		this.stimulusUnit = stimulusUnit;
	}

	public Double getStimulusValue() {
		return this.stimulusValue;
	}

	public void setStimulusValue(Double stimulusValue) {
		this.stimulusValue = stimulusValue;
	}

	public String getSourceText() {
		return this.sourceText;
	}

	public void setSourceText(String sourceText) {
		this.sourceText = sourceText;
	}

	public String getSourceType() {
		return this.sourceType;
	}

	public void setSourceType(String sourceType) {
		this.sourceType = sourceType;
	}

	public String getSourceUnit() {
		return this.sourceUnit;
	}

	public void setSourceUnit(String sourceUnit) {
		this.sourceUnit = sourceUnit;
	}

	public Double getSourceValue() {
		return this.sourceValue;
	}

	public void setSourceValue(Double sourceValue) {
		this.sourceValue = sourceValue;
	}

	public String getArtifactText() {
		return this.artifactText;
	}

	public void setArtifactText(String artifactText) {
		this.artifactText = artifactText;
	}

	public String getArtifactType() {
		return this.artifactType;
	}

	public void setArtifactType(String artifactType) {
		this.artifactType = artifactType;
	}

	public String getArtifactUnit() {
		return this.artifactUnit;
	}

	public void setArtifactUnit(String artifactUnit) {
		this.artifactUnit = artifactUnit;
	}

	public Double getArtifactValue() {
		return this.artifactValue;
	}

	public void setArtifactValue(Double artifactValue) {
		this.artifactValue = artifactValue;
	}

	public String getEnvironmentText() {
		return this.environmentText;
	}

	public void setEnvironmentText(String environmentText) {
		this.environmentText = environmentText;
	}

	public String getEnvironmentType() {
		return this.environmentType;
	}

	public void setEnvironmentType(String environmentType) {
		this.environmentType = environmentType;
	}

	public String getEnvironmentUnit() {
		return this.environmentUnit;
	}

	public void setEnvironmentUnit(String environmentUnit) {
		this.environmentUnit = environmentUnit;
	}

	public Double getEnvironmentValue() {
		return this.environmentValue;
	}

	public void setEnvironmentValue(Double environmentValue) {
		this.environmentValue = environmentValue;
	}

	public String getResponseText() {
		return this.responseText;
	}

	public void setResponseText(String responseText) {
		this.responseText = responseText;
	}

	public String getResponseType() {
		return this.responseType;
	}

	public void setResponseType(String responseType) {
		this.responseType = responseType;
	}

	public String getResponseUnit() {
		return this.responseUnit;
	}

	public void setResponseUnit(String responseUnit) {
		this.responseUnit = responseUnit;
	}

	public Double getResponseValue() {
		return this.responseValue;
	}

	public void setResponseValue(Double responseValue) {
		this.responseValue = responseValue;
	}

	public String getMeasureText() {
		return this.measureText;
	}

	public void setMeasureText(String measureText) {
		this.measureText = measureText;
	}

	public String getMeasureType() {
		return this.measureType;
	}

	public void setMeasureType(String measureType) {
		this.measureType = measureType;
	}

	public String getMeasureUnit() {
		return this.measureUnit;
	}

	public void setMeasureUnit(String measureUnit) {
		this.measureUnit = measureUnit;
	}

	public Double getMeasureValue() {
		return this.measureValue;
	}

	public void setMeasureValue(Double measureValue) {
		this.measureValue = measureValue;
	}

	public String getState() {
		return this.state;
	}

	public void setState(String state) {
		this.state = state;
	}

	public String getReasoningFramework() {
		return this.reasoningFramework;
	}

	public void setReasoningFramework(String reasoningFramework) {
		this.reasoningFramework = reasoningFramework;
	}

	public boolean equals(Object anotherScenario) {

		if (anotherScenario == null)
			return (false);

		if (anotherScenario instanceof ArchEScenario) {
			Integer scenarioUid = ((ArchEScenarioVO)anotherScenario).getUid();
			if ((scenarioUid != null) && (uid != null)) {
				if (scenarioUid.intValue() == uid.intValue())
					return (true);
				else if (anotherScenario != null) {
					if (((ArchEScenarioVO)anotherScenario).getFactId().equals(factId))
						return (true);
					// TODO: The comparison using getFactId() exposes Jess implementation details 
				}
			}
		}

		return (this == anotherScenario);
	}

	public String getName() {
		return ("ArchEScenario-"+this.getId());
	}
	
}
